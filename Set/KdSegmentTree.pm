
package Set::KdSegmentTree;

require Exporter;

@ISA    = qw(Exporter);
@EXPORT = qw(add_interval make_tree
  query_point query_overlap query_window
  debug_dump_tree
);

use strict;

sub new {
    my ($class, $max_level) = @_;
    return bless {
        values    => [],
        max_level => $max_level,
        debug     => 0
    };
}

sub debug {
    my ( $self, $debug ) = @_;
    $self->{debug} = $debug;
}

sub _bld_bintree {
    my ( $values, $len ) = @_;
    my @_sorted = ($len);

    sub _trv_c {
        my ( $values, $len, $idx, $sorted, $order) = @_;
        $order = _trv_c( $values, $len, 2 * $idx, $sorted, $order) if 2 * $idx <= $len;
        my $val = $values->[$order-1];
        $sorted->[$idx] = [$val,0,0,0,0];
        $order ++;
        $order = _trv_c( $values, $len, 2 * $idx + 1, $sorted, $order) if 2 * $idx + 1 <= $len;
        return $order;
    }
    _trv_c( $values, $len, 1, \@_sorted, 1);

    sub _leaf_min {
        my ($values, $len, $idx) = @_;
        return _leaf_min($value, $len, 2*$idx) if (2 * $idx <= $len);
        my $node = $value->[$idx];
        return $node->[0];
    }
    sub _leaf_max {
        my ($values, $len, $idx) = @_; 
        return _leaf_max($value, $len, 2*$idx+1) if (2 * $idx + 1<= $len);
        my $node = $value->[$idx];
        return $node->[0];
    }
    map {
        my $node = $_sorted[$_];
        $node->[3] = _leaf_min(\@_sorted, $len, $_);
        $node->[4] = _leaf_max(\@_sorted, $len, $_);
    } (1..$len);
    return \@_sorted;
}

sub add_interval {
    my ( $self, $bounds, $value ) = @_;
    my $values = $self->{values};
    push( @$values, [ $bounds, $value ] );
}

sub _add_val {
    my ( $bin_tree, $idx, $min, $max, $value, $lvl ) = @_;
    my $a    = $value->[0][ 2 * $lvl ];
    my $b    = $value->[0][ 2 * $lvl + 1 ];
    my $node = $bin_tree->[ $idx];
    my $len  = $bin_tree->[0];
    my $sep  = $node->[0];

    if ($idx > $len) {
        return;
    }

    if ( $a == $sep and $sep == $b) {
        #only one node
        $node->[2] = [] if (0 eq $node->[2]);
        push( @{ $node->[2] }, $value );
        return;
    }
    if ( $a == $sep or $sep == $b ) {
        $node->[2] = [] if $node->[2] == undef;
        push( @{ $node->[2] }, $value );
    }
    if ( $a <= $min and $max <= $b ) {
        $node->[1] = [] if $node->[1] == undef;
        push( @{ $node->[1] }, $value );
        return;
    }
    _add_val( $bin_tree, 2 * $idx, $min, $sep, $value, $lvl )
          if ( $a < $sep );
    _add_val( $bin_tree, 2 * $idx + 1, $sep, $max, $value, $lvl )
          if ( $sep < $b );
}

sub make_tree {
    my ($self)    = @_;
    my $values    = $self->{values};
    my $max_level = $self->{max_level};
    my @que       = ();
    my $subtrees = [];
    my $debug = $self->{debug};

    push( @que, [ $values, 0, $subtrees] );
    while ( scalar(@que) > 0 ) {
        my $item        = pop(@que);
        my $uniq_points = {};
        my $boxes       = $item->[0];
        my $lvl         = $item->[1];
        my $subcont     = $item->[2];
        map {
            my $a = $_->[0]->[ 2 * $lvl ];
            my $b = $_->[0]->[ 1 + 2 * $lvl ];
            $uniq_points->{$a}++;
            $uniq_points->{$b}++;
        } @$boxes;
        my @points = sort { $a - $b } keys %$uniq_points;
        if ( $self->{debug} ) {
            printf( "level %d: ", $lvl );
            map { printf( "%5d ", $_ ); } @points;
            printf( ": %d\n", scalar(@points) );
        }
        my $key_cnt = scalar(@points);
        my $sorted = _bld_bintree( \@points, scalar(@points) );
        map {
            my $min = scalar($points[0]);
            my $max = scalar($points[$key_cnt-1]);
            _add_val( $sorted, 1, $min, $max, $_, $lvl);
        } @$boxes;
        push(@$subcont, $sorted);

        map {
            my $node      = $sorted->[ $_];
            my $sub_match = $node->[1];
            my $ext_match = $node->[2];
            if ( $self->{debug} ) {
                my $match_cnt = 0;
                $match_cnt += scalar(@$sub_match) if ( $sub_match != undef );
                $match_cnt += scalar(@$ext_match) if ( $ext_match != undef );
                if ( $match_cnt != 0 ) {
                    printf( "%2d %5d", $_, $node->[0] );
                    printf( " sub:%d", scalar(@$sub_match) )
                      if undef != $sub_match;
                    printf( " ext:%d", scalar(@$ext_match) )
                      if undef != $ext_match;
                    printf("\n");
                }
            }

            if ( 1+$lvl < $max_level ) {
                if (defined($sub_match) and (0 != $sub_match) ) {
                    my $subtree = [];
                    push( @que, [ $sub_match, $lvl + 1, $subtree] );
                    $node->[1] = $subtree;
                }
                if (defined($ext_match) and (0 != $ext_match) ) {
                    my $subtree = [];
                    push( @que, [ $ext_match, $lvl + 1, $subtree] );
                    $node->[2] = $subtree;
                }
            }
        } ( 1 .. ( 1 + 2 * $key_cnt ) );
    }
    printf("subtree count : %d\n", scalar(@$subtrees)) if $self->{debug};
    $self->{subtree} = $subtrees->[0];
}

sub _query_tree {
    my ($tree, $lvl, $points) = @_;
    my $loc = $points->[$lvl];
    my @ret = ();
    my @que = (1);
    my $len = $tree->[0];
    while (scalar(@que)>0) {
        my $idx = pop(@que);
        my $node = $tree->[$idx];
        my $sep = $node->[0];
        my $min = $node->[3];
        my $max = $node->[4];
        if ($min <= $loc and $loc <= $max) {
            if (defined($node->[1]) and (0 != $node->[1])) {
                if ($lvl+1 < $max_lvl) {
                    push(@ret, $node->[1]->[0]);
                } else {
                    my $vals = $node->[1];
                    map { push(@ret, $_) } @$vals;
                }
            }
            if ($loc == $sep) {
                if (defined($node->[2]) and (0 != $node->[2])) {
                    if (defined($node->[2]) and (0 != $node->[2])) {
                        push(@ret, $node->[2]->[0]);
                    } else {
                        my $vals = $node->[2];
                        map { push(@ret, $_) } @$vals;
                    }
                }
            }
            if ($loc < $sep) {
                push(@que, 2*$idx) if 2*$idx<=$len;
            } elsif ($loc > $sep) {
                push(@que, 2*$idx+1) if 1+2*$idx<=$len;
            }
        }
    }
    return \@ret;
}

sub query_point {
    my ( $self, $points ) = @_;
    my $subtree = $self->{subtree};
    my $max_lvl = $self->{max_level};
    my @que = ();
    my @ret = {};
    my $debug = $self->{debug};
    push(@que, [$subtree, 0]);
    while ( scalar(@que) > 0 ) {
        my $item = pop(@que);
        my $tree = $item->[0];
        my $lvl  = $item->[1];
        my $trees = _query_tree($tree, $lvl, $points);
        map {
            if ($lvl+1 < $max_lvl) {
                printf(" %8x : %d lvl\n", $_, $lvl+1) if $debug;
                push(@que, [$_, $lvl+1]) ;
            } else {
                print $_, "\n" if $debug;
                $ret->{$_} = $_->[1];
            }
        } @$trees;
    }
    my @boxes = values %$ret;
    return \@ret;
}

sub debug_dump {
    my ($self) = @_;

    my $values = $self->{values};
    my $max_level = $self->{max_level};
    printf("max_level: %d\n", $max_level);
    map {
        my $boxes = $_->[0];
        my $desc = $_->[1];
        map { 
            printf("[%5d, %5d] ", $boxes->[2*$_], $boxes->[1+2*$_]);
        } (0..$max_level-1);
        print " ", $desc, "\n";
    } @$values;
    my @que = ([$self->{subtree},0]);
    printf("search trees:\n");
    while(@que) {
        my $item = pop(@que);
        my $tree = $item->[0];
        my $lvl = $item->[1];
        my $len = $tree->[0];
        printf("tree : %x (%d internal nodes, %d total)\n", $tree, 
                $len, scalar(@$tree));

        for my $idx (1..$len) {
            my $node = $tree->[$idx];
            printf(" node-%02d %5d [%d,%d]", $idx, $node->[0], $node->[3], $node->[4]);
            if (defined($node->[1]) and (0 != $node->[1])) {
                if (1+$lvl < $self->{max_level}) {
                    my $subtree = $node->[1][0];
                    printf(" (%8x %8x)", $subtree, $subtree->[0]);
                    push(@que, [$subtree, $lvl+1]);
                } else {
                    my $vals = $node->[1];
                    printf(" (%08x ", $vals);
                    map {  print '"',$_->[1], '",'} @$vals;
                    print ")";
                }
            } else {
                printf(" (%8x %8x)", 0, 0);
            }
            if (defined($node->[2]) and (0 != $node->[2])) {
                if (1+$lvl < $self->{max_level}) {
                    my $subtree = $node->[2][0];
                    printf(" (%8x %8x)", $subtree, $subtree->[0]);
                    push(@que, [$subtree, $lvl+1]);
                } else {
                    my $vals = $node->[2];
                    printf(" (%08x ", $vals);
                    map {  print '"',$_->[1], '",'} @$vals;
                    print ")";
                }
            } else {
                printf(" (%8x %8x)", 0, 0);
            }
            printf("\n");
        }
    }
}

BEGIN {
}

1
