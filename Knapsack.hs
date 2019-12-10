{-# LANGUAGE DeriveFunctor #-}
module Knapsack where

import qualified Data.Heap as H
import Data.Maybe

type Goods = [(Int, Double)]

{- backtracking -}
knapsack0 :: Goods -> Int -> Double
knapsack0 [] _ = 0
knapsack0 ((w', v'):goods) w
  | w' < w    = max (knapsack0 goods w) (knapsack0 goods (w - w') + v')
  | otherwise = knapsack0 goods w

-- >>> knapsack0 [(2, 6.0), (2, 3.0), (6, 5.0), (5, 4.0), (4, 6.0)] 10
-- 15.0
--

{- dynamic programming -} 
knapsack1 :: Goods -> Int -> Double
knapsack1 goods w = head $ go goods w where
  go []              0 = [0]
  go (wv:goods)      0 = 0 : go goods w
  go []              w = 0 : go []    (w-1)
  go ((w',v'):goods) rest
    | w' > rest  = let memo = go ((w',v'):goods) (rest-1) in memo !! w : memo
    | otherwise = let memo = go ((w',v'):goods) (rest-1)
                      v1  = memo !! w
                      v2  = memo !! (w' + w)
                      new = max v1 (v2 + v')
                  in  new : memo

-- >>> knapsack1 [(2, 6.0), (2, 3.0), (6, 5.0), (5, 4.0), (4, 6.0)] 10
-- 15.0
--

data Solution = Solution 
  { boundOf :: Double
  , wCount  :: Int
  , vCount  :: Double
  , collected :: Int
  } deriving (Eq, Show)

instance Ord Solution where
  compare a b = compare (boundOf a) (boundOf b)

{- branch and bound -} 
knapsack2 :: Goods -> Int -> Double
knapsack2 []    _ = 0
knapsack2 goods w = go 0 0 (H.singleton $ Solution (bound goods) 0 0 0) where
  bound goods = sum (map snd goods)

  go best res queue =
    case H.uncons queue of
      Nothing -> res
      Just (solution, queue)
        | boundOf solution < best            -> go best res queue
        | collected solution == length goods -> go (boundOf solution) (vCount solution) queue
        | otherwise -> 
          let c = collected solution in
          let newBound = bound (drop c goods) + vCount solution in
          let s1 = solution {
            wCount = wCount solution + fst (goods !! c),
            vCount = vCount solution + snd (goods !! c),
            collected = collected solution + 1
          } in
          let s2 = solution {
            boundOf = boundOf solution - snd (goods !! c),
            collected = collected solution + 1
          } in 
          if wCount solution + fst (goods !! c) <= w && boundOf solution <= newBound
            then go best res $ H.insert s2 (H.insert s1 queue)
            else go best res $ H.insert s2 queue

-- >>> knapsack2 [(2, 6.0), (2, 3.0), (6, 5.0), (5, 4.0), (4, 6.0)] 10
-- 15.0
--

newtype Mu f = In { out :: f (Mu f) }
type Algebra f a = f a -> a
type CoAlgebra f a = a -> f a
type CVAlgebra f a = f (Attr f a) -> a

data Attr f a = Attr 
  {   attribute :: a --memorize
  ,   hole :: f (Attr f a) 
  } deriving (Functor)


cata :: Functor f => Algebra f a -> Mu f -> a -- catamorphism
cata alg = alg . fmap (cata alg) . out

ana :: Functor f => CoAlgebra f a -> a -> Mu f
ana g = a where a = In . fmap a . g

hylo :: Functor f => CoAlgebra f a -> Algebra f b -> a -> b
hylo g f = f . fmap (hylo g f) . g
  -- cata f . ana g

histo :: Functor f => CVAlgebra f a -> Mu f -> a -- histomorphism
histo alg = attribute . h where  
  h = uncurry Attr . (\a -> (alg a, a)) . fmap h . out

dyna :: Functor f => CoAlgebra f a -> CVAlgebra f b -> a -> b
dyna psi phi = attribute . h where
  h = uncurry Attr . (\a -> (phi a, a)) . fmap h . psi
  -- histo phi . ana psi


data KnapsackF a
  = Empty
  | Skip a
  | Select Double a a
  deriving(Functor)

{- backtracking by using hylomorphism -}
knapsack3 :: Goods -> Int -> Double
knapsack3 = curry $ hylo phi psi where
  phi :: CoAlgebra KnapsackF (Goods, Int)
  phi ([], _) = Empty
  phi ((w', v'):goods, w)
    | w' > w    = Skip (goods, w)
    | otherwise = Select v' (goods, w) (goods, w - w')

  psi :: Algebra KnapsackF Double
  psi Empty = 0
  psi (Skip v) = v
  psi (Select v v1 v2) = max v1 (v2 + v)

-- >>> knapsack3 [(2, 6.0), (2, 3.0), (6, 5.0), (5, 4.0), (4, 6.0)] 10
-- 15.0
--

data ListF e a
  = Last e
  | Cons e a
  deriving (Functor, Eq, Show)

lookupCache :: Attr (ListF e) a -> Integer -> Maybe a
lookupCache cache 0 = Just (attribute cache)
lookupCache cache n =
  case hole cache of
    Last _      -> Nothing
    Cons _ next -> lookupCache next (n - 1)

data KnapsackDPF a
  = Init
  | First a
  | Next Int Int Double a
  deriving(Functor)

{- dynamic programming by using hylomorphism -}
knapsack4 :: Goods -> Int -> Double
knapsack4 goods w = head $ hylo phi psi (goods, w) where
  phi :: CoAlgebra KnapsackDPF (Goods, Int)
  phi ([], 0)             = Init
  phi (wv:goods, 0)       = First (goods, w)
  phi ([], w)             = First ([], w - 1)
  phi ((w', v'):goods, w) = Next w' w v' ((w',v'):goods, w - 1)

  psi :: Algebra KnapsackDPF [Double]
  psi Init = [0]
  psi (First memo) = 0 : memo
  psi (Next w' rest v' memo) 
    | w' > rest  = memo !! w : memo
    | otherwise =
      let v1  = memo !! w
          v2  = memo !! (w' + w)
          new = max v1 (v2 + v')
      in  new : memo


-- >>> knapsack4 [(2, 6.0), (2, 3.0), (6, 5.0), (5, 4.0), (4, 6.0)] 10
-- 15.0
--

{- dynamic programming by using dynamorphism -}
knapsack5 :: Goods -> Int -> Double
knapsack5 goods w = dyna phi psi (goods, w) where
  phi :: CoAlgebra (ListF (Goods, Int)) (Goods, Int)
  phi ([], 0)       = Last ([], 0)
  phi (wv:goods, 0) = Cons (wv:goods, 0) (goods, w)
  phi (goods, w)    = Cons (goods, w) (goods, w - 1)

  psi :: CVAlgebra (ListF (Goods, Int)) Double
  psi (Last _)         = 0
  psi (Cons ([], _) _) = 0
  psi (Cons ((w', v'):goods', rest) memo) 
    | w' > rest  = fromJust $ lookupCache memo (toInteger w)  -- memo[i-1][w]
    | otherwise =
      let v1 = fromJust $ lookupCache memo (toInteger w)      
          v2 = fromJust $ lookupCache memo (toInteger (w' + w)) -- memo[i-1][w - w']
      in  max v1 (v2 + v')

-- >>> knapsack5 [(2, 6.0), (2, 3.0), (6, 5.0), (5, 4.0), (4, 6.0)] 10
-- 15.0
--

data KnapsackBBF a
  = Res Double
  | Queue a
  deriving(Functor)


{- branch and bound by using hylomorphism -}
knapsack6 :: Goods -> Int -> Double
knapsack6 goods w = hylo phi psi (0, 0, H.singleton $ Solution (bound goods) 0 0 0) where
  bound goods = sum (map snd goods)

  phi :: CoAlgebra KnapsackBBF (Double, Double, H.Heap Solution)
  phi (best, res, queue) = 
    case H.uncons queue of
      Nothing -> Res res
      Just (solution, queue)
        | boundOf solution < best            -> Queue(best, res, queue)
        | collected solution == length goods -> Queue(boundOf solution, vCount solution, queue)
        | otherwise -> 
          let c = collected solution in
          let newBound = bound (drop c goods) + vCount solution in
          let s1 = solution {
            wCount = wCount solution + fst (goods !! c),
            vCount = vCount solution + snd (goods !! c),
            collected = collected solution + 1
          } in
          let s2 = solution {
            boundOf = boundOf solution - snd (goods !! c),
            collected = collected solution + 1
          } in 
          if wCount solution + fst (goods !! c) <= w && boundOf solution <= newBound
            then Queue(best, res, H.insert s2 $ H.insert s1 queue)
            else Queue(best, res, H.insert s2 queue)

  psi :: Algebra KnapsackBBF Double
  psi (Res res) = res
  psi (Queue v) = v

-- >>> knapsack6 [(2, 6.0), (2, 3.0), (6, 5.0), (5, 4.0), (4, 6.0)] 10
-- 15.0
--