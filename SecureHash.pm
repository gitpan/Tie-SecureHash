package Tie::SecureHash;

use strict;
use vars qw($VERSION $strict $fast);
use Carp;

$VERSION = '1.03';

sub import
{
	my $pkg = shift;
	foreach (@_) { $strict ||= /strict/; $fast ||= /fast/ }
	croak qq{$pkg can't be both "strict" and "fast"} if $strict && $fast;
}

# TAKE A LIST OF POSSIBLE CLASSES FOR AN IMPLICIT KEY AND REMOVE NON-CONTENDERS

sub _winnow
{
	my ($caller, $nonpublic, @classes) = @_;

	# REMOVE CLASSES NOT IN HIERARCHY FOR NON-PUBLIC KEY

	@classes = grep { $caller->isa($_) } @classes if $nonpublic;

	# COMPARE REMAINING KEYS PAIRWISE, ELIMINATING "SHADOWED" KEYS...

	I: for(my $i=0; $i<$#classes; )
	{
		J: for(my $j=$i+1; $j<@classes; )
		{
			if ($classes[$j]->isa($classes[$i]))
			{
			# CLASS J SHADOWS I FROM $caller
				if ($caller->isa($classes[$j]))
				{
					splice @classes,$i,1;
					next I;
				}
			# CLASS J BELOW CALLING PACKAGE
			# (SO CALLING PACKAGE COULDN'T INHERIT IT)
				elsif($classes[$j]->isa($caller))
				{
					splice @classes,$j,1;
					next J;
				}
			}
			elsif ($classes[$i]->isa($classes[$j]))
			{
			# CLASS I SHADOWS J FROM $caller
				if ($caller->isa($classes[$i]))
				{
					splice @classes,$j,1;
					next J;
				}
			# CLASS I BELOW CALLING PACKAGE
			# (SO CALLING PACKAGE COULDN'T INHERIT IT)
				elsif($classes[$i]->isa($caller))
				{
					splice @classes,$i,1;
					next I;
				}
			}
			$j++;

		}
		$i++;
	}

	return @classes;
};

# DETERMINE IF A KEY IS ACCESSIBLE

sub _access	# ($self,$key,$caller)
{
	my ($self, $key, $caller, $file, $delete) = @_;

	# EXPLICIT KEYS...

	if ($key =~ /\A([\w:]*)::((_{0,2})[^:]+)\Z/)
	{
		my ($classname, $shortkey, $mode) = ($1,$2,$3);
		unless ($classname)
		{
			$classname = 'main';
			$key = $classname.$key;
		}
		if ($mode eq '__')	# PRIVATE
		{
			croak "Private key $key of tied securehash inaccessible from package $caller"
				unless $classname eq $caller;
			if (exists $self->{fullkeys}{$key})
			{
				croak "Private key $key of tied securehash inaccessible from file $file"
					if $self->{file}{$key} ne $file;
			}
			else
			{
				if ($delete) { delete $self->{file}{$key} }
				else { $self->{file}{$key} = $file }
			}
		}
		elsif ($mode eq '_')	# PROTECTED
		{
			croak "Protected key $key of tied securehash inaccessible from package $caller"
				unless $caller->isa($classname);
		}

		if (!exists $self->{fullkeys}{$key})
		{
			croak "Entry for key $key of tied securehash cannot be created " .
			      "from package $caller"
				if $classname ne $caller && !$delete;
			if ($delete)
			{
				@{$self->{keylist}{$shortkey}} =
					grep { $_ !~ /$classname/ }
						@{$self->{keylist}{$shortkey}}
			}
			else
			{
				push @{$self->{keylist}{$shortkey}}, $classname;
			}
		}
	}

	# IMPLICIT PRIVATE KEY (MUST BE IN CALLING CLASS)
	elsif ($key =~ /\A(__[^:]+)\Z/)
	{
		carp qq{Accessing securehash via unqualified key {"$key"}\n}.
		     qq{will circumvent 'fast' mode. Use {"${caller}::$key"}}
			if $strict;
		if (!exists $self->{fullkeys}{"${caller}::$key"})
		{
			croak "Private key '$key' of tied securehash is inaccessible from package $caller"
				if exists $self->{keylist}{$key};
			croak "Private key '${caller}::$key' does not exist in tied securehash"
		}
		$key = "${caller}::$key";	
		if (exists $self->{fullkeys}{$key})
		{
			croak "Private key $key of tied securehash inaccessible from file $file"
				if $self->{file}{$key} ne $file;
		}
	}

	# IMPLICIT PROTECTED OR PUBLIC KEY
	# (PROTECTED KEY MUST BE IN ANCESTRAL HIERARCHY OF CALLING CLASS)
	elsif ($key =~ /\A((_?)[^:]+)\Z/)
	{
		my $fullkey = "${caller}::$key";	
		carp qq{Accessing securehash via unqualified key {"$key"}\n}.
		     qq{will be unsafe in 'fast' mode. Use {"${caller}::$key"}}
			if $strict;
		if (exists $self->{fullkeys}{$fullkey})
		{
			$key = $fullkey;
		}
		else
		{
			my @classes = _winnow($caller, $2,
						 @{$self->{keylist}{$key}||[]});
	
			if (@classes)
			{
				# TOO MANY CHOICES
				croak "Ambiguous key '$key' (when accessed "
				      . "from package $caller).\nCould be:\n"
				      . join("", map {"\t${_}::$key\n"} @classes)
				      . " " 
					if @classes > 1;
				$key = $classes[0]."::$key";
			}
			else	# NOT ENOUGH CHOICES
			{
				croak +($2?"Protected":"Public")." key '$key' of tied securehash is inaccessible from package $caller"
					if exists $self->{keylist}{$key};
				croak +($2?"Protected":"Public")." key '${caller}::$key' does not exist in tied securehash";
			}
		}
	}
	else	# INVALID KEY 
	{
		croak "Invalid key '$key'";
	}

	if ($delete) { return delete $self->{fullkeys}{$key}; }	
	return \$self->{fullkeys}{$key};

};


# NOTE THAT NEW MAY TIE AND BLESS INTO THE SAME CLASS
# IF NOTHING MORE APPROPRIATE IS SPECIFIED

sub new
{
	my %self = ();
	my $class =  ref($_[0])||$_[0];
	my $blessclass =  ref($_[1])||$_[1]||$class;
	my $impl = tie %self, $class unless $fast;
	my $self = bless \%self, $blessclass;
	splice(@_,0,2);
	if (@_)		# INITIALIZATION ARGUMENTS PRESENT
	{
		my ($ancestor, $file);
		my $i = 0;
		while ( ($ancestor,$file) = caller($i++) )
		{
			last if $ancestor eq $blessclass;
		}
		my ($key, $value);
		while (($key,$value) = splice(@_,0,2))
		{
			my $fullkey = $key=~/::/ ? $key : "${blessclass}::$key";
			if ($fast)
			{
				$self->{$fullkey} = $value;
			}
			else
			{
				$impl->{fullkeys}{$fullkey} = $value;
				push @{$impl->{keylist}{$key}}, $blessclass;
				$impl->{file}{$fullkey} = $file
					if $key =~ /\A__/;
			}
		}
	}

	return $self;
}

# USEFUL METHODS TO DUMP INFORMATION

sub debug
{
	my $self = tied %{$_[0]};
	my ($caller, $file, $line, $sub) = (caller,(caller(1))[3]||"(none)");
	return _simple_debug($_[0],$caller, $file, $line, $sub) unless $self;
	my ($key, $val);
	my %sorted = ();
	while ($key = each %{$self->{fullkeys}})
	{
		$key =~ m/\A(.*?)([^:]*)\Z/;
		push @{$sorted{$1}}, $key;
	}

	print STDERR "\nIn subroutine '$sub' called from package '$caller' ($file, line $line):\n";
	foreach my $class (keys %sorted)
	{
		print STDERR "\n\t$class\n";
		foreach $key ( @{$sorted{$class}} )
		{
			print STDERR "\t\t";
			my ($shortkey) = $key =~ /.*::(.*)/;
			my $explanation = "";
			if (eval { _access($self,$shortkey,$caller, $file); 1 })
			{
				print STDERR '(+)';
			}
			elsif ($@ =~ /\AAmbiguous key/)
			{
				print STDERR '(?)';
				($explanation = $@) =~ s/.*\n//;
				$explanation =~ s/.*\n\Z//;
				$explanation =~ s/\ACould/Ambiguous unless fully qualified. Could/;
				$explanation =~ s/^(?!\Z)/\t\t\t>>> /gm;
			}
			else
			{
				print STDERR '(-)';
				if ($shortkey =~ /\A__/ && $@ =~ /file/)
				{
					$explanation = "\t\t\t>>> Private entry of $class\n\t\t\t>>> declared in file $self->{file}{$key}\n\t\t\t>>> is inaccessable from file $file.\n"
				}
				elsif ($shortkey =~ /\A__/)
				{
					$explanation = "\t\t\t>>> Private entry of $class\n\t\t\t>>> is inaccessable from package $caller.\n"
				}
				else
				{
					$explanation = "\t\t\t>>> Protected entry of $class\n\t\t\t>>> is inaccessible outside its hierarchy (i.e. from $caller).\n"
				}
				
			}
			my $val = $self->{fullkeys}{$key};
			if (defined $val) { $val = "'$val'" }
			else { $val = "undef" }
			print STDERR " '$shortkey'\t=> $val";
			print STDERR "\n$explanation" if $explanation;
			print STDERR "\n";
		}
	}
}

sub _simple_debug
{
	my ($self,$caller, $file, $line, $sub) = @_;
	my ($key, $val);
	my %sorted = ();
	while ($key = each %{$self})
	{
		$key =~ m/\A(.*?)([^:]*)\Z/;
		push @{$sorted{$1}}, $key;
	}

	print "\nIn subroutine '$sub' called from package '$caller' ($file, line $line):\n";
	foreach my $class (keys %sorted)
	{
		print "\n\t$class\n";
		foreach $key ( @{$sorted{$class}} )
		{
			print "\t\t";
			print " '$key'\t=> '$self->{$key}'\n";
		}
	}
}


sub each	{ each %{$_[0]} }
sub keys	{ keys %{$_[0]} }
sub values	{ values %{$_[0]} }
sub exists	{ exists $_[0]->{$_[1]} }

sub TIEHASH	# ($class, @args)
{
	my $class = ref($_[0]) || $_[0];
	if ($strict)
	{
		carp qq{Tie'ing a securehash directly will be unsafe in 'fast' mode.\n}.
		     qq{Use Tie::SecureHash::new instead}
			unless (caller 1)[3] =~ /\A(.*?)::([^:]*)\Z/
			    && $2 eq "new"
			    && $1->isa('Tie::SecureHash');
	}
	elsif ($fast)
	{
		carp qq{Tie'ing a securehash directly should never happen in 'fast' mode.\n}.
		     qq{Use Tie::SecureHash::new instead}
	}
	bless {}, $class;
}

sub FETCH	# ($self, $key)
{
	my ($self, $key) = @_;
	my $entry = _access($self,$key,(caller)[0..1]);
	return $$entry if $entry;
	return;
}

sub STORE	# ($self, $key, $value)
{
	my ($self, $key, $value) = @_;
	my $entry = _access($self,$key,(caller)[0..1]);
	return $$entry = $value if $entry;
	return;
}

sub DELETE	# ($self, $key)
{
	my ($self, $key) = @_;
	return _access($self,$key,(caller)[0..1],'DELETE');
}

sub CLEAR	# ($self)
{
	my ($self) = @_;
	my ($caller, $file) = caller;
	my @inaccessibles =
		grep { ! eval { _access($self,$_,$caller,$file); 1 } }
			keys %{$self->{fullkeys}};
	croak "Unable to assign to securehash because the following existing keys\nare inaccessible from package $caller and cannot be deleted:\n" .
		join("\n", map {"\t$_"} @inaccessibles) . "\n "
			if @inaccessibles;
	%{$self} = ();
}

sub EXISTS	# ($self, $key)
{
	my ($self, $key) = @_;
	my @context = (caller)[0..1];
	eval { _access($self,$key,@context); 1 } ? 1 : '';
}

sub FIRSTKEY	# ($self)
{
	my ($self) = @_;
	keys %{$self->{fullkeys}};
	goto &NEXTKEY;
}

sub NEXTKEY	# ($self)
{
	my $self = $_[0];
	my $key;
	my @context = (caller)[0..1];
	while (defined($key = each %{$self->{fullkeys}}))
	{
		last if eval { _access($self,$key,@context) };
	}
	return $key;
}

sub DESTROY	# ($self)
{
	# NOTHING TO DO
	# (BE CAREFUL SINCE IT DOES DOUBLE DUTY FOR tie AND bless)
}


1;
__END__

=head1 NAME

Tie::SecureHash - A tied hash that supports namespace-based encapsulation

=head1 VERSION

This document describes version 1.00 of Tie::SecureHash,
released December 3, 1998

=head1 SYNOPSIS

    use Tie::SecureHash;

    # CREATE A SECURE HASH

	my %hash;
	tie %hash, Tie::SecureHash;

    # CREATE A REFERENCE TO A SECURE HASH (BLESSED INTO Tie::SecureHash!)

	my $hashref = Tie::SecureHash->new();

    # CREATE A REFERENCE TO A SECURE HASH (BLESSED INTO $some_other_class)

	my $hashref = Tie::SecureHash->new($some_other_class);

    # CREATE NEW ENTRIES IN THE HASH

	package MyClass;

	sub new
	{
		my ($class, %args) = @_
		my $self = Tie::SecureHash->($class);

		$self->{MyClass::public}     = $args{public};
		$self->{MyClass::_protected} = $args{protected};
		$self->{MyClass::__private}  = $args{private};

		return $self;
	}

    # SAME EFFECT, EASIER SYNTAX...

	package MyClass;

	sub new
	{
		my ($class, %args) = @_
		my $self = Tie::SecureHash->($class,
				public     => $args{public},
				_protected => $args{protected},
				__private  => $args{private},
				);

		return $self;
	}


    # ACCESS RESTRICTIONS ON ENTRIES

	package MyClass;

	sub print_attributes
	{
	    my $self = $_[0];
					# OKAY? (ACCESSIBLE WHERE?)

	    print $self->{public};	#  YES  (ANYWHERE)
	    print $self->{_protected};	#  YES  (ONLY IN MyClass HIERARCHY)
	    print $self->{__private};	#  YES  (ONLY IN MyClass)
	}


	package SonOfMyClass; @ISA = qw( MyClass );

	sub print_attributes
	{
	    my $self = $_[0];
					# OKAY? (ACCESSIBLE WHERE?)

	    print $self->{public};	#  YES  (ANYWHERE)
	    print $self->{_protected};	#  YES  (ONLY IN MyClass HIERARCHY)
	    print $self->{__private};	#  NO!  (ONLY IN MyClass)
	}


	package main;

	my $object = MyClass->new();
					# OKAY? (ACCESSIBLE WHERE?)

	print $object->{public};	#  YES  (ANYWHERE)
	print $object->{_protected};	#  NO!  (ONLY IN MyClass HIERARCHY)
	print $object->{__private};	#  NO!  (ONLY IN MyClass)


    # DEBUGGING

	$object->Tie::SecureHash::debug();


=head1 DESCRIPTION

[Coming soon]

=head1 DIAGNOSTICS

=over 4

=item C<Private key %s of tied securehash inaccessible from package %s>

Private keys can only be accessed from their "owner" package. An
attempt was made to access a private key from some other package.

=item C<Private key %s of tied securehash inaccessible from file %s>

Private keys can only be accessed from the lexical scope of the file in which
they were originally declared. An attempt was made
to access a private key from some lexical scope (probably another file, but
perhaps an C<eval>).

=item C<Protected key %s of tied securehash inaccessible from package %s>

Protected keys can only be accessed from theie "owner" package and any
of its subclasses. An attempt was made to access a protected key from
some package not in the owner's inheritance hierarchy.


=item C<Entry for key %s of tied securehash cannot be created from package %s>

Keys must be declared from within the lexical scope of their owner's package.
In other words, the qualifier for a key declaration must be the same as the
current package. An attempt was made to declare a key from some package other
than its owner.

=item C<Private key %s does not exist in tied securehash>

Securehash keys are not autovivifying; they must be declared using a
fully qualified key before they can be used. An attempt was made to
access or assign to an unqualified private key (one with two
leading underscores), before the corresponding fully qualified key
was declared.

=item C<Protected key %s does not exist in tied securehash>

Securehash keys are not autovivifying; they must be declared using a
fully qualified key before they can be used. An attempt was made to
access or assign to an unqualified protected key (one with a single
leading underscore), before the corresponding fully qualified key
was declared.

=item C<Public key %s does not exist in tied securehash>

Securehash keys are not autovivifying; they must be declared using a
fully qualified key before they can be used. An attempt was made to
access or assign to an unqualified public key (one with no leading
underscore), before the corresponding fully qualified key was declared.

=item C<Ambiguous key %s (when accessed from package %s). Could be: %s>

An unqualified key was used to access the securehash, but it was ambiguous
in the context. The error message lists the set of fully qualified keys that
might have matched.

=item C<Invalid key %s>

An attempt was made to access the securehash (or declare a key) through an
improperly formatted key. This almost always means that the qualifier isn't a
valid package name.

=item C<%s can't be both "strict" and "fast">

Tie::SecureHash detected that both the $Tie::SecureHash::strict and
$Tie::SecureHash::fast keys were set. But the two modes are mutually exclusive.

=item C<Accessing securehash via unqualified key %s will be unsafe in 'fast' mode. Use %s::%s>

This warning is issued in "strict" mode, and points out an access attempt which
will break if the code is converted to "fast" mode.

=item C<Tie'ing a securehash directly will circumvent 'fast' mode. Use Tie::SecureHash::new instead>

This warning is issued in "strict" mode, and points out an explicit
C<tie> to the Tie::SecureHash module. Hashes tied in this way will not
speed up under "fast" mode.

=item C<Tie'ing a securehash directly should never happen in 'fast' mode. Use Tie::SecureHash::new instead>

This warning is issued in "fast" mode, and points out an explicit
C<tie> to the Tie::SecureHash module. Hashes tied in this way will still
be slow. This diagnostic can be turned off by setting $Tie::SecureHash::fast to
any value other than 1.

=item C<Unable to assign to securehash because the following existing keys are inaccessible from package %s and cannot be deleted: %s>

An attempt was made to assign a completely new set of entries to a securehash.
Typically something like this:

	%securehash = ();

This doesn't work unless all the existing keys are accessible at the point of
the assignment.


=head1 AUTHOR

Damian Conway (damian@cs.monash.edu.au)

=head1 BUGS AND IRRITATIONS

There are undoubtedly serious bugs lurking somewhere in this code :-)
Bug reports and other feedback are most welcome.

=head1 COPYRIGHT

        Copyright (c) 1998-2000, Damian Conway. All Rights Reserved.
      This module is free software. It may be used, redistributed
      and/or modified under the terms of the Perl Artistic License
           (see http://www.perl.com/perl/misc/Artistic.html)
