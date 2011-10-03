#!/usr/bin/perl

package Set::KdIntervalTree;

require Exporter;

@ISA    = qw(Exporter);
@EXPORT = qw(add_interval make_tree
  query_point query_overlap query_window
  debug_dump
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
        $sorted->[$idx] = [$val,0,0];
        $order ++;
        $order = _trv_c( $values, $len, 2 * $idx + 1, $sorted, $order) if 2 * $idx + 1 <= $len;
        return $order;
    }
    _trv_c( $values, $len, 1, \@_sorted, 1);
    #map { push( @_sorted, [] ); } ( 1 .. ( 1+$len ) );
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

    #printf("%2d [%5d-%5d-%5d] [%d %d]\n", $idx, $min, $sep, $max, $a, $b);
    if ( $a == $sep or $sep == $b ) {
        $node->[2] = [] if $node->[2] == undef;
        push( @{ $node->[2] }, $value );
        #printf("%2d [%5d-%5d-%5d] [%d %d] - ext\n", $idx, $min, $sep, $max, $a, $b);
    }
    if ( $a <= $min and $max <= $b ) {
        $node->[1] = [] if $node->[1] == undef;
        push( @{ $node->[1] }, $value );
        #printf("%2d [%5d-%5d-%5d] [%d %d] - ext\n", $idx, $min, $sep, $max, $a, $b);
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
        #map { print @points->[$_],','} (0..scalar(@points)-1); printf "\n";
        my $sorted = _bld_bintree( \@points, scalar(@points) );
        map {
            _add_val( $sorted, 1, @points[0], @points[ $key_cnt - 1 ],
                $_, $lvl );
        } @$boxes;
        #push(@$subtrees, $sorted);
        #printf("tree: %x, len %x\n", $sorted,$sorted->[0]);
        push(@$subcont, $sorted);

        #printf( "level %d: %d\n", $lvl, scalar(@$sorted) ) if $self->{debug};
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
                if ( undef != $sub_match ) {
                    my $subtree = [];
                    push( @que, [ $sub_match, $lvl + 1, $subtree] );
                    $node->[1] = $subtree;
                }
                if ( undef != $ext_match ) {
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
    while (scalar(@que)>0) {
        my $idx = pop(@que);
        my $len = $tree->[0];
        my $node = $tree->[$idx];
        my $sep = $node->[0];
        #printf(" %8x %2d %5d : %d %x %x\n", $tree, $idx, $sep, $loc,
        #        $node->[1], $node->[2]);
        push(@ret, $node->[1]->[0])if $node->[1] != undef;
        if ($loc == $sep) {
            push(@ret, $node->[2]->[0])if $node->[2] != undef;
        }
        if ($loc < $sep) {
            push(@que, 2*$idx) if 2*$idx<=$len;
        } elsif ($loc > $sep) {
            push(@que, 2*$idx+1) if 1+2*$idx<=$len;
        }
    }
    #printf(" %8x          : %d ret\n", $tree, scalar(@ret));
    return \@ret;
}

sub query_point {
    my ( $self, $points ) = @_;
    my $subtree = $self->{subtree};
    my @que = ();
    my @ret = ();
    push(@que, [$subtree, 0]);
    while ( scalar(@que) > 0 ) {
        my $item = pop(@que);
        my $tree = $item->[0];
        my $lvl  = $item->[1];
        my $trees = _query_tree($tree, $lvl, $points);
        map {
            if ($lvl+1 < $self->{max_level}) {
                #printf(" %8x          : %d lvl\n", $_, $lvl+1);
                push(@que, [$_, $lvl+1]) ;
            } else {
                #printf(" %8x          : \n", $_);
                push(@ret, $_);
            }
        } @$trees;
    }
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
            printf(" node-%02d %5d", $idx, $node->[0]);
            if (undef != $node->[1]) {
                my $subtree = $node->[1][0];
                printf(" (%8x %8x)", $subtree, $subtree->[0]);
                push(@que, [$subtree, $lvl+1]) if (1+$lvl < $self->{max_level});
            } else {
                printf(" (%8x %8x)", 0, 0);
            }
            if (undef != $node->[2]) {
                my $subtree = $node->[2][0];
                printf(" (%8x %8x)", $subtree, $subtree->[0]);
                push(@que, [$subtree, $lvl+1]) if (1+$lvl < $self->{max_level});
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
