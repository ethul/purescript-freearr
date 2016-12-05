-- | This module defines a free arrows.
-- |
-- | The implementation of this module is based on Exequiel Rivas and Mauro
-- | Jaskelioff's work.
-- |
-- | See [Notions of Computation as Monoids](http://www.fceia.unr.edu.ar/~mauro/pubs/Notions_of_Computation_as_Monoids.pdf) (Rivas and Jaskelioff 2016)
module Control.Arrow.Free
  ( Free
  , NaturalTransformation'
  , type (~~>)
  , liftFreeArr
  , foldFreeArr
  ) where

import Prelude

import Data.Exists (Exists, runExists, mkExists)
import Data.Profunctor (class Profunctor, dimap, arr)
import Data.Profunctor.Strong (class Strong, (***), first)
import Data.Tuple (Tuple(..))

data Free a x y = Hom (x -> y) | Comp (Exists (Comp' a x y))

data Comp' a x y z = Comp' (a x z) (Free a z y)

type NaturalTransformation' p q = forall x y. p x y -> q x y

infixr 4 type NaturalTransformation' as ~~>

comp' :: forall a x y z. a x z -> Free a z y -> Comp' a x y z
comp' = Comp'

comp :: forall a x y z. a x z -> Free a z y -> Free a x y
comp x y = Comp (mkExists (comp' x y))

liftFreeArr :: forall a. Profunctor a => a ~~> Free a
liftFreeArr x = comp x (arr id)

foldFreeArr :: forall a b. (Profunctor b, Category b) => (a ~~> b) -> Free a ~~> b
foldFreeArr k (Hom f) = arr f
foldFreeArr k (Comp e) = runExists (\(Comp' x y) -> foldFreeArr k y <<< k x) e

instance semigroupoidFree :: Profunctor a => Semigroupoid (Free a) where
  compose c (Hom f) = dimap f id c
  compose c (Comp e) = runExists (\(Comp' x y) -> comp x (c <<< y)) e

instance categoryFree :: Profunctor a => Category (Free a) where
  id = Hom id

instance profunctorFree :: Profunctor a => Profunctor (Free a) where
  dimap f g (Hom h) = Hom (g <<< h <<< f)
  dimap f g (Comp e) = runExists (\(Comp' x y) -> comp (dimap f id x) (dimap id g y)) e

instance strongFree :: Strong a => Strong (Free a) where
  first (Hom f) = Hom (\(Tuple x z) -> Tuple (f x) z)
  first (Comp e) = runExists (\(Comp' x y) -> comp (first x) (first y)) e
  second = (***) id
