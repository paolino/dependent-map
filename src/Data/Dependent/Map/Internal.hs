{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Safe #-}
#endif
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE PolyKinds #-}
#endif
module Data.Dependent.Map.Internal where

import Data.GADT.Compare
import Data.Some
#if MIN_VERSION_base(4,7,0)
import Data.Typeable (Typeable)
#endif
import Data.Dependent.Sum
-- |Dependent maps: 'k' is a GADT-like thing with a facility for 
-- rediscovering its type parameter, elements of which function as identifiers
-- tagged with the type of the thing they identify.  Real GADTs are one
-- useful instantiation of @k@, as are 'Tag's from "Data.Unique.Tag" in the 
-- 'prim-uniq' package.
--
-- Semantically, @'DMap' k f@ is equivalent to a set of @'r' k f@ where no two
-- elements have the same tag.
--
-- More informally, 'DMap' is to dependent products as 'M.Map' is to @(->)@.
-- Thus it could also be thought of as a partial (in the sense of \"partial
-- function\") dependent product.
data DMap c k f where
    Tip :: DMap c k f
    Bin :: {- sz    -} !Int
        -> {- key   -} !(DSum c k f)
        -> {- left  -} !(DMap c k f)
        -> {- right -} !(DMap c k f)
        -> DMap c k f
#if MIN_VERSION_base(4,7,0)
    deriving Typeable
#endif

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- | /O(1)/. The empty map.
--
-- > empty      == fromList []
-- > size empty == 0
empty :: DMap c k f
empty = Tip

-- | /O(1)/. A map with a single element.
--
-- > singletonD 1 'a'        == fromList [(1, 'a')]
-- > size (singletonD 1 'a') == 1
singletonD :: DSum c k f  -> DMap c k f
singletonD kx = Bin 1 kx Tip Tip

singleton :: c v => k v -> f v -> DMap c k f
singleton k x = singletonD (k :=> x)
{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}


-- | /O(1)/. Is the map empty?
null :: DMap c k f -> Bool
null Tip    = True
null Bin{}  = False

-- | /O(1)/. The number of elements in the map.
size :: DMap c k f -> Int
size Tip                = 0
size (Bin n _  _ _)    = n


-- | /O(log n)/. Lookup the value at a key in the map.
--
-- The function will return the corresponding value as @('Just' value)@,
-- or 'Nothing' if the key isn't in the map.
lookup :: forall c k f v
    . GCompare k     
    => k v -> DMap c k f -> Maybe (f v)
lookup k = k `seq` go
    where
        go ::  DMap c k f -> Maybe (f v)
        go Tip = Nothing
        go (Bin _ (kx :=> x) l r) = 
            case gcompare k kx of
                GLT -> go l
                GGT -> go r
                GEQ -> Just x
lookupAssoc :: forall c k f v
    .  GCompare k 
    => Some k 
    -> DMap c k f 
    -> Maybe (DSum c k f)
lookupAssoc (This k) = k `seq` go
  where
    go ::  DMap c k f -> Maybe (DSum c k f)
    go Tip = Nothing
    go (Bin _ kx@(k' :=> _) l r) =
        case gcompare k k' of
            GLT -> go l
            GGT -> go r
            GEQ -> Just kx

{-
-}
{--------------------------------------------------------------------
  Utility functions that maintain the balance properties of the tree.
  All constructors assume that all values in [l] < [k] and all values
  in [r] > [k], and that [l] and [r] are valid trees.
  
  In order of sophistication:
    [Bin sz k x l r]  The type constructor.
    [bin k x l r]     Maintains the correct size, assumes that both [l]
                      and [r] are balanced with respect to each other.
    [balance k x l r] Restores the balance and size.
                      Assumes that the original tree was balanced and
                      that [l] or [r] has changed by at most one element.
    [combine k x l r] Restores balance and size. 

  Furthermore, we can construct a new tree from two trees. Both operations
  assume that all values in [l] < all values in [r] and that [l] and [r]
  are valid:
    [glue l r]        Glues [l] and [r] together. Assumes that [l] and
                      [r] are already balanced with respect to each other.
    [merge l r]       Merges two trees and restores balance.

  Note: in contrast to Adam's paper, we use (<=) comparisons instead
  of (<) comparisons in [combine], [merge] and [balance]. 
  Quickcheck (on [difference]) showed that this was necessary in order 
  to maintain the invariants. It is quite unsatisfactory that I haven't 
  been able to find out why this is actually the case! Fortunately, it 
  doesn't hurt to be a bit more conservative.
--------------------------------------------------------------------}

{-
-}
{--------------------------------------------------------------------
  Combine
--------------------------------------------------------------------}
combine :: GCompare k => DSum c k f -> DMap c k f -> DMap c k f -> DMap c k f
combine kx Tip r  = insertMin kx r
combine kx l Tip  = insertMax kx l
combine kx l@(Bin sizeL ky ly ry) r@(Bin sizeR kz lz rz)
  | delta*sizeL <= sizeR  = balance kz  (combine kx  l lz) rz
  | delta*sizeR <= sizeL  = balance ky ly (combine kx ry r)
  | otherwise             = bin kx  l r


-- insertMin and insertMax don't perform potentially expensive comparisons.
insertMax,insertMin :: DSum c k f  -> DMap c k f -> DMap c k f
insertMax kx t
  = case t of
      Tip -> singletonD kx 
      Bin _ ky l r
          -> balance ky l (insertMax kx r)
             
insertMin kx  t
  = case t of
      Tip -> singletonD kx 
      Bin _ ky l r
          -> balance ky  (insertMin kx l) r
             
{--------------------------------------------------------------------
  [merge l r]: merges two trees.
--------------------------------------------------------------------}
merge :: DMap c k f -> DMap c k f -> DMap c k f
merge Tip r   = r
merge l Tip   = l
merge l@(Bin sizeL kx lx rx) r@(Bin sizeR ky  ly ry)
  | delta*sizeL <= sizeR = balance ky (merge l ly) ry
  | delta*sizeR <= sizeL = balance kx lx (merge rx r)
  | otherwise            = glue l r

{--------------------------------------------------------------------
  [glue l r]: glues two trees together.
  Assumes that [l] and [r] are already balanced with respect to each other.
--------------------------------------------------------------------}
glue :: DMap c k f -> DMap c k f -> DMap c k f
glue Tip r = r
glue l Tip = l
glue l r   
  | size l > size r = case deleteFindMax l of (km,l') -> balance km l' r
  | otherwise       = case deleteFindMin r of (km,r') -> balance km l r'

-- | /O(log n)/. Delete and find the minimal element.
--
-- > deleteFindMin (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((3,"b"), fromList[(5,"a"), (10,"c")]) 
-- > deleteFindMin                                            Error: can not return the minimal element of an empty map
deleteFindMin :: DMap c k f -> (DSum c k f, DMap c k f)
deleteFindMin t = case minViewWithKey t of
      Nothing -> (error "Map.deleteFindMin: can not return the minimal element of an empty map", Tip)
      Just p -> p
-- | A strict pair.
data (:*:) a b = !a :*: !b
infixr 1 :*:

-- | Convert a strict pair to a pair.
toPair :: a :*: b -> (a, b)
toPair (a :*: b) = (a, b)
{-# INLINE toPair #-}
data Triple' a b c = Triple' !a !b !c

-- | Convert a strict triple to a triple.
toTriple :: Triple' a b c -> (a, b, c)
toTriple (Triple' a b c) = (a, b, c)
{-# INLINE toTriple #-}
-- | /O(log n)/. Retrieves the minimal (key :=> value) entry of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
minViewWithKey :: forall c k f  . DMap c k f -> Maybe (DSum c k f, DMap c k f)
minViewWithKey Tip = Nothing
minViewWithKey (Bin _ k0x0 l0 r0) = Just $! toPair $ go k0x0 l0 r0
    where
    go :: DSum c k f -> DMap c k f -> DMap c k f -> DSum c k f :*: DMap c k f
    go kx Tip r = kx :*: r
    go kx (Bin _ k1x1 ll lr) r =
      let !(km :*: l') = go k1x1 ll lr
      in (km :*: balance kx l' r)

-- | /O(log n)/. Retrieves the maximal (key :=> value) entry of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
maxViewWithKey :: forall c k f . DMap c k f -> Maybe (DSum c k f, DMap c k f)
maxViewWithKey Tip = Nothing
maxViewWithKey (Bin _ k0x0 l0 r0) = Just $! toPair $ go k0x0 l0 r0
  where
    go :: DSum c k f -> DMap c k f -> DMap c k f -> DSum c k f :*: DMap c k f
    go kx l Tip = kx :*: l
    go kx l (Bin _ krxr rl rr) =
      let !(km :*: r') = go krxr  rl rr
      in (km :*: balance kx l r')
-- | /O(log n)/. Delete and find the maximal element.
--
-- > deleteFindMax (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((10,"c"), fromList [(3,"b"), (5,"a")])
-- > deleteFindMax empty                                      Error: can not return the maximal element of an empty map

deleteFindMax :: DMap c k f -> (DSum c k f, DMap c k f)
deleteFindMax t
  = case t of
      Bin _ kx l Tip -> (kx,l)
      Bin _ kx l r   -> let (km,r') = deleteFindMax r in (km,balance kx l r')
      Tip             -> (error "Map.deleteFindMax: can not return the maximal element of an empty map", Tip)


{--------------------------------------------------------------------
  [balance l x r] balances two trees with value x.
  The sizes of the trees should balance after decreasing the
  size of one of them. (a rotation).

  [delta] is the maximal relative difference between the sizes of
          two trees, it corresponds with the [w] in Adams' paper.
  [ratio] is the ratio between an outer and inner sibling of the
          heavier subtree in an unbalanced setting. It determines
          whether a double or single rotation should be performed
          to restore balance. It is correspondes with the inverse
          of $\alpha$ in Adam's article.

  Note that:
  - [delta] should be larger than 4.646 with a [ratio] of 2.
  - [delta] should be larger than 3.745 with a [ratio] of 1.534.
  
  - A lower [delta] leads to a more 'perfectly' balanced tree.
  - A higher [delta] performs less rebalancing.

  - Balancing is automatic for random data and a balancing
    scheme is only necessary to avoid pathological worst cases.
    Almost any choice will do, and in practice, a rather large
    [delta] may perform better than smaller one.

  Note: in contrast to Adam's paper, we use a ratio of (at least) [2]
  to decide whether a single or double rotation is needed. Allthough
  he actually proves that this ratio is needed to maintain the
  invariants, his implementation uses an invalid ratio of [1].
--------------------------------------------------------------------}

balance :: DSum c k f  -> DMap c k f -> DMap c k f -> DMap c k f
balance kx l r
  | sizeL + sizeR <= 1    = Bin sizeX kx l r
  | sizeR >= delta*sizeL  = rotateL kx l r
  | sizeL >= delta*sizeR  = rotateR kx l r
  | otherwise             = Bin sizeX kx l r
  where
    sizeL = size l
    sizeR = size r
    sizeX = sizeL + sizeR + 1

delta,ratio :: Int
delta = 4
ratio = 2
-- rotate
rotateL :: DSum c k f -> DMap c k f -> DMap c k f -> DMap c k f
rotateL kx l r@(Bin  _ _ ly ry)
  | size ly < ratio*size ry = singleL kx l r
  | otherwise               = doubleL kx l r
rotateL  _ _ Tip = error "rotateL Tip"

rotateR :: DSum c k f  -> DMap c k f -> DMap c k f -> DMap c k f
rotateR kx l@(Bin  _ _ ly ry) r
  | size ry < ratio*size ly = singleR kx l r
  | otherwise               = doubleR kx l r
rotateR  _ Tip _ = error "rotateR Tip"

-- basic rotations
singleL, singleR :: DSum c k f -> DMap c k f -> DMap c k f -> DMap c k f
singleL k1x1 t1 (Bin _ k2x2 t2 t3)  = bin k2x2 (bin k1x1 t1 t2) t3
singleL  _ _ Tip = error "singleL Tip"
singleR k1x1 (Bin _ k2x2 t1 t2) t3  = bin k2x2 t1 (bin k1x1 t2 t3)
singleR  _ Tip _ = error "singleR Tip"

doubleL, doubleR :: DSum c k f  -> DMap c k f -> DMap c k f -> DMap c k f
doubleL k1x1 t1 (Bin _ k2x2 (Bin _ k3x3 t2 t3) t4) 
    = bin (k3x3) (bin k1x1 t1 t2) (bin (k2x2) t3 t4)
doubleL  _ _ _ = error "doubleL"
doubleR k1x1 (Bin _ k2x2 t1 (Bin _ k3x3 t2 t3)) t4 
    = bin (k3x3) (bin (k2x2) t1 t2) (bin k1x1 t3 t4)
doubleR _ _ _ = error "doubleR"
{--------------------------------------------------------------------
  The bin constructor maintains the size of the tree
--------------------------------------------------------------------}
bin :: DSum c k f -> DMap c k f -> DMap c k f -> DMap c k f
bin kx l r
  = Bin (size l + size r + 1) kx l r
{--------------------------------------------------------------------
  Utility functions that return sub-ranges of the original
  tree. Some functions take a comparison function as argument to
  allow comparisons against infinite values. A function [cmplo k]
  should be read as [compare lo k].

  [trim cmplo cmphi t]  A tree that is either empty or where [cmplo k == LT]
                        and [cmphi k == GT] for the key [k] of the root.
  [filterGt cmp t]      A tree where for all keys [k]. [cmp k == LT]
  [filterLt cmp t]      A tree where for all keys [k]. [cmp k == GT]

  [split k t]           Returns two trees [l] and [r] where all keys
                        in [l] are <[k] and all keys in [r] are >[k].
  [splitLookup k t]     Just like [split] but also returns whether [k]
                        was found in the tree.
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  [trim lo hi t] trims away all subtrees that surely contain no
  values between the range [lo] to [hi]. The returned tree is either
  empty or the key of the root is between @lo@ and @hi@.
--------------------------------------------------------------------}
trim ::  (Some k -> Ordering) -> (Some k -> Ordering) -> DMap c k f -> DMap c k f
trim _     _     Tip = Tip
trim cmplo cmphi t@(Bin _ (kx :=> _) l r)
  = case cmplo (This kx) of
      LT -> case cmphi (This kx) of
              GT -> t
              _  -> trim cmplo cmphi l
      _  -> trim cmplo cmphi r
              
trimLookupLo :: GCompare k 
    
    => Some k -> (Some k -> Ordering) -> DMap c k f -> (Maybe (DSum c k f), DMap c k f)
trimLookupLo _  _     Tip = (Nothing,Tip)
trimLookupLo lo cmphi t@(Bin _ kxx@(kx :=> _) l r)
  = case compare lo (This kx) of
      LT -> case cmphi (This kx) of
              GT -> (lookupAssoc lo t, t)
              _  -> trimLookupLo lo cmphi l
      GT -> trimLookupLo lo cmphi r
      EQ -> (Just kxx, trim (compare lo) cmphi r)


{--------------------------------------------------------------------
  [filterGt k t] filter all keys >[k] from tree [t]
  [filterLt k t] filter all keys <[k] from tree [t]
--------------------------------------------------------------------}
filterGt :: GCompare k 
    
    => (Some k -> Ordering) -> DMap c k f -> DMap c k f
filterGt cmp = go
  where
    go Tip              = Tip
    go (Bin _ kxx@(kx :=> _)  l r) = case cmp (This kx) of
              LT -> combine kxx (go l) r
              GT -> go r
              EQ -> r

filterLt 
    :: GCompare k 
    
    => (Some k -> Ordering) -> DMap c k f -> DMap c k f
filterLt cmp = go
  where
    go Tip              = Tip
    go (Bin _ kxx@(kx :=> _) l r) = case cmp (This kx) of
          LT -> go l
          GT -> combine kxx l (go r)
          EQ -> l
{-
-}

