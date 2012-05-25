--
-- Copyright (c) 2012, Anders Persson
-- All rights reserved.
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
--
--     * Redistributions of source code must retain the above copyright notice,
--       this list of conditions and the following disclaimer.
--     * Redistributions in binary form must reproduce the above copyright
--       notice, this list of conditions and the following disclaimer in the
--       documentation and/or other materials provided with the distribution.
--     * Neither the name of Anders Persson nor the names of other contributors
--       may be used to endorse or promote products derived from this software
--       without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
-- IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
-- DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
-- FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
-- DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
-- SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
-- CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
-- OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
--

{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}

module Feldspar.Complexity
where

import Prelude hiding (max)

import Debug.Trace

import Data.Typeable

import Control.Monad.Reader
import Control.Monad.State
import Data.Dynamic

import Language.Syntactic
import Language.Syntactic.Constructs.Decoration (stripDecor)

import Feldspar hiding (drawAST, trace, max)
import Feldspar.Core.Constructs hiding (Data)
import Feldspar.Core.Interpretation

import Feldspar.Core.Constructs.Array
import Feldspar.Core.Constructs.Binding
import Feldspar.Core.Constructs.Bits
import Feldspar.Core.Constructs.Complex
import Feldspar.Core.Constructs.Condition
import Feldspar.Core.Constructs.ConditionM
import Feldspar.Core.Constructs.Conversion
import Feldspar.Core.Constructs.Eq
import Feldspar.Core.Constructs.Error
import Feldspar.Core.Constructs.Floating
import Feldspar.Core.Constructs.Fractional
import Feldspar.Core.Constructs.Integral
import Feldspar.Core.Constructs.Literal
import Feldspar.Core.Constructs.Logic
import Feldspar.Core.Constructs.Loop
import Feldspar.Core.Constructs.Mutable
import Feldspar.Core.Constructs.MutableArray
import Feldspar.Core.Constructs.MutableReference
import Feldspar.Core.Constructs.MutableToPure
import Feldspar.Core.Constructs.Num
import Feldspar.Core.Constructs.Ord
import Feldspar.Core.Constructs.Trace
import Feldspar.Core.Constructs.Tuple

-- | Classify variables carrying @Data@ or @Size@ information. Any expression depending on a
-- @Data@ variable is also classified as Data
--
data Sort = Data  -- ^ The variable carries data
          | Size  -- ^ The variable carries size information
  deriving (Show)

classify :: Sort -> Sort -> Sort
classify Data _    = Data
classify _    Data = Data
classify _    _    = Size

type CountM a = ReaderT [(VarId,Sort)] (State VarId) a

freshVar :: CountM VarId
freshVar = do
  v <- get
  let v' = v - 1
  put v'
  return v'

isSizeVar :: VarId -> CountM Bool
isSizeVar v = do
  vars <- ask
  case lookup v vars of
    Just sz -> return True
    _       -> return False

class Count subDomain
  where
    countSym :: ( Count domain
                , NUM :<: domain
                , Literal TypeCtx :<: domain
                , Variable TypeCtx :<: domain
                , Lambda TypeCtx :<: domain
                , Let TypeCtx TypeCtx :<: domain
                , Loop :<: domain
                , Array :<: domain
                , ORD :<: domain
                , Signature a
                )
             => Sort -> subDomain a -> Args (AST domain) a -> CountM (Sort, ASTF domain WordN)
    countSym = countSymDefault

countSymDefault sort feat args = do (ss,cs) <- liftM unzip $ sequence $ listArgs (count' sort) args
                                    return (foldr classify Size ss, foldr add zero cs)

instance (Count sub1, Count sub2) => Count (sub1 :+: sub2)
  where
    countSym sort (InjL a) args = countSym sort a args
    countSym sort (InjR a) args = countSym sort a args

add :: (NUM :<: dom, Literal TypeCtx :<: dom) => ASTF dom WordN -> ASTF dom WordN -> ASTF dom WordN
add a b = case (prjCtx typeCtx a, prjCtx typeCtx b) of
            (Just (Literal 0), _               ) -> b
            (_               , Just (Literal 0)) -> a
            (Just (Literal x), Just (Literal y)) -> appSymCtx typeCtx (Literal (x + y))
            _                                    -> inj Add :$ a :$ b

mul :: (NUM :<: dom) => ASTF dom WordN -> ASTF dom WordN -> ASTF dom WordN
mul = appSym Mul

zero :: (Literal TypeCtx :<: dom) => ASTF dom WordN
zero = sugarSymCtx typeCtx (Literal 0)

one :: (Literal TypeCtx :<: dom) => ASTF dom WordN
one = sugarSymCtx typeCtx (Literal 1)

variable :: (Variable TypeCtx :<: dom) => VarId -> ASTF dom WordN
variable v = appSymCtx typeCtx (Variable v)

max :: (ORD :<: dom) => ASTF dom WordN -> ASTF dom WordN -> ASTF dom WordN
max = appSym Max

lambda :: ( Type a
          , Typeable b
          , Lambda TypeCtx :<: dom
          )
       => VarId -> ASTF dom b -> ASTF dom (a -> b)
lambda v = appSymCtx typeCtx (Lambda v)

let_ :: ( Type a
        , Type b
        , Let TypeCtx TypeCtx :<: dom
        )
     => ASTF dom a -> ASTF dom (a -> b) -> ASTF dom b
let_ = appSym (letBind typeCtx)

count' :: ( Count dom
          , NUM :<: dom
          , Literal TypeCtx :<: dom
          , Variable TypeCtx :<: dom
          , Lambda TypeCtx :<: dom
          , Let TypeCtx TypeCtx :<: dom
          , Loop :<: dom
          , Array :<: dom
          , ORD :<: dom
          )
       => Sort -> ASTF dom a -> CountM (Sort, ASTF dom WordN)
count' sort = queryNodeSimple (countSym sort)

class (Typeable b) => CountTop a b | a -> b
  where
    countTop :: ( Count dom
                , NUM :<: dom
                , Literal TypeCtx :<: dom
                , Variable TypeCtx :<: dom
                , Lambda TypeCtx :<: dom
                , Let TypeCtx TypeCtx :<: dom
                , Loop :<: dom
                , Array :<: dom
                , ORD :<: dom
                )
             => Sort -> ASTF dom a -> CountM (Sort, ASTF dom b)

instance (CountTop b c, d ~ (Length -> c)) => CountTop (a -> b) d
  where
    countTop sort (lam :$ f)
      | Just (Lambda v) <- prjCtx typeCtx lam
      = do
          (s,body) <- local ((v,Size):) $ countTop sort f
          return $ (s, lambda v $ body)

instance (d ~ WordN) => CountTop a d
  where
    countTop sort a = count' sort a

count :: ( CountTop a b
         , Count dom
         , Literal TypeCtx :<: dom
         , Lambda TypeCtx :<: dom
         , Variable TypeCtx :<: dom
         , Let TypeCtx TypeCtx :<: dom
         , Loop :<: dom
         , Array :<: dom
         , NUM :<: dom
         , ORD :<: dom
         )
      => ASTF dom a -> (Sort, ASTF dom b)
count a = flip evalState 0 $ flip runReaderT [] $ (countTop Size) a

instance Count NUM
  where
    countSym sort Add args = do (ss, cs) <- liftM unzip $ sequence $ listArgs (count' sort) args
                                return $ (foldr classify Size ss, foldr add one cs)
    countSym sort Mul args = do (ss, cs) <- liftM unzip $ sequence $ listArgs (count' sort) args
                                return $ (foldr classify Size ss, foldr add one cs)
    countSym sort Sub args = do (ss, cs) <- liftM unzip $ sequence $ listArgs (count' sort) args
                                return $ (foldr classify Size ss, foldr add one cs)
    countSym sort feat args = countSymDefault sort feat args

instance (Count dom) => Count (Decor Info (Lambda TypeCtx :+: Variable TypeCtx :+: dom))
  where
    countSym sort (Decor _ a) args = countSym sort a args

instance Count Loop
  where
    countSym sort ForLoop (len :* init :* (lam1 :$ (lam2 :$ body)) :* Nil)
      | Just (Lambda ix)  <- prjCtx typeCtx lam1
      , Just (Lambda st)  <- prjCtx typeCtx lam2
      = do
          (sl, l') <- count' Size len
          (si, i') <- count' Size init
          state <- case si of
            Size -> return st
            _    -> freshVar
          local ((ix, sl):) $ local ((st,si):) $ do
            (sb, b') <- count' Data body
            return $ (sl, inj ForLoop
              :$ l'
              :$ zero
              :$ (lambda ix $ lambda state $ (variable state `add` b')))

    countSym sort feat args = trace "default Loop" $ countSymDefault sort feat args

instance Count Array
  where
    countSym sort Parallel (len :* (lam :$ body) :* Nil)
      | Just (Lambda ix) <- prjCtx typeCtx lam
      = do
          (sl,l') <- count' Size len
          (sb,b') <- local ((ix,Size):) $ count' Data body
          state <- freshVar
          return $ (Size,inj ForLoop :$ l' :$ zero :$
            (lambda ix $ lambda state $ (variable state `add` b')))

    countSym Size GetLength (arr :* Nil)
      | Just (Variable v) <- prjCtx typeCtx arr
      = do
          s <- isSizeVar v
          if s then return (Size, variable v)
               else return (Data, zero)

    countSym Data GetLength (arr :* Nil)
      = return (Data, zero)

    countSym Size GetIx (arr :* ix :* Nil)
      | Just (Variable a)  <- prjCtx typeCtx arr
      = count' Size ix
    countSym Data GetIx (arr :* ix :* Nil)
      = return (Data, zero)

    countSym sort feat args = trace ("default Array: ") $ countSymDefault sort feat args

instance Count (Let TypeCtx TypeCtx)
  where
    countSym sort Let (a :* (lam :$ body) :* Nil)
      | Just (Lambda v) <- prjCtx typeCtx lam
      = do
          (sa, a') <- count' sort a
          (sb, b') <- local ((v,sa):) $ count' sort body
          return $ (sb, a' `add` (let_ zero (lambda v $ b')))

instance Count (Variable TypeCtx)
  where
    countSym Size (Variable v) Nil
      = do
          s <- isSizeVar v
          if s then return (Size, variable v)
               else return (Data, zero)

    countSym sort feat args = countSymDefault sort feat args

instance Count (Condition TypeCtx)
  where
    countSym sort Condition (c :* t :* e :* Nil)
      = do
          (sc, c') <- count' Size c
          (st, t') <- count' Data t
          (se, e') <- count' Data e
          return $ (classify sc (classify st se), c' `add` (max t' e'))

instance Count (Lambda TypeCtx)
instance Count BITS
instance Count COMPLEX
instance Count (ConditionM IO)
instance Count Conversion
instance Count EQ
instance Count Error
instance Count FLOATING
instance Count FRACTIONAL
instance Count INTEGRAL
instance Count (Literal TypeCtx)
instance Count Logic
instance Count (LoopM IO)
instance Count (MONAD IO)
instance Count Mutable
instance Count MutableArray
instance Count MutableReference
instance Count MutableToPure
instance Count ORD
instance Count Trace
instance Count (Tuple TypeCtx)
instance Count (Select TypeCtx)


