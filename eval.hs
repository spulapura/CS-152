{-# LANGUAGE QuasiQuotes #-}

import Data.Map (Map)
import Data.Monoid
import qualified Data.Map as Map
import Data.SExp
import Control.Monad
import Control.Applicative

-- The abstract syntax of a lambda language with printing
data Exp =
    Var String            -- x
  | Lambda String Exp     -- (lambda (x) e)
  | App Exp Exp           -- (e1 e2)
  | StringLit String      -- "foo"
  | Concat Exp Exp        -- (concat e1 e2)
  | Output Exp            -- (output e)
  | UnitLit               -- unit
  deriving (Eq, Ord, Show)

-- Values that expressions evaluate to
data Val =
    Closure String Exp Env
  | StringVal String
  | UnitVal
  deriving (Eq, Ord, Show)

-- The variable environment, mapping variables to values
type Env = Map String Val

-- ### BEGIN Part 1 ###

-- A monad which supports failure and output effects
-- (you should replace Undefined)
data MaybeWriter w a = MaybeWriter (Maybe (a, w))

-- ### END Part 1 ###

-- ### BEGIN Part 2 ###

mwReturn :: (Monoid w) => a -> MaybeWriter w a
mwReturn x = MaybeWriter(Just (x, mempty))

mwBind :: (Monoid w) => MaybeWriter w a -> (a -> MaybeWriter w b) -> MaybeWriter w b
mwBind (MaybeWriter mW) f = 
  case mW of
    Nothing -> MaybeWriter(Nothing)
    Just(x, w1) -> let MaybeWriter(Just(y, w2)) = f x in MaybeWriter(Just(y, mappend w1 w2))



mwFailure :: (Monoid w) => MaybeWriter w a
mwFailure = MaybeWriter(Nothing)

mwOutput :: (Monoid w) => w -> MaybeWriter w ()
mwOutput x = MaybeWriter(Just((), x))

-- ### END Part 2 ###

instance (Monoid w) => Monad (MaybeWriter w) where
  return = mwReturn
  (>>=) = mwBind

instance (Monoid w) => Functor (MaybeWriter w) where
  fmap = liftM 

instance (Monoid w) => Applicative (MaybeWriter w) where
  pure = return
  (<*>) = ap

-- ### BEGIN put your helpers here ###

coerceS :: Val -> MaybeWriter String String
coerceS (StringVal s) = return s
coerceS _ = mwFailure

coerceC :: Val -> MaybeWriter String (String, Exp, Env)
coerceC (Closure x e env) = return (x,e,env)
coerce _ = mwFailure


-- ### END put your helpers here ###

-- ### BEGIN Part 3 ###

-- (evalM e env) evaluates 'e' in the environment 'env' to a final value inside
-- the MaybeWriter monad.  The monoid which the monad manipulates is a String,
-- which is the output that accumulates during evaluation.
evalM :: Exp -> Env -> MaybeWriter String Val
evalM (UnitLit) env = return (UnitVal)
evalM (StringLit s) env = return (StringVal s)
evalM (Var x) env = 
  case Map.lookup x env of
    Nothing -> mwFailure
    Just str -> return str
evalM (Lambda x e) env = return (Closure x e env)
evalM (App e1 e2) env = do
  v1 <- evalM e1 env
  (x,e,env2) <- coerceC v1
  v2 <- evalM e2 env
  v <- evalM e (Map.insert x v2 env2)
  return v 
evalM (Concat e1 e2) env = do
  v1 <- evalM e1 env >>= coerceS 
  v2 <- evalM e2 env >>= coerceS 
  return (StringVal(v1 ++ v2))
evalM (Output e) env = do
  s <- evalM e env >>= coerceS
  mwOutput s
  return (UnitVal)




-- ### END Part 3 ###

-- ### BEGIN Part 4 ###

-- (eval e env) evaluates 'e' in the environment 'env' to a final pure result.
--
-- The result is either Nothing, indicating failure, or Just (v, out)
-- indicating a result value 'v' with global output 'out'.
eval :: Exp -> Env -> Maybe (Val, String)
eval exp env = let MaybeWriter(mW) = evalM exp env in mW 

-- ### END Part 4 ###

-- A few simple examples.
-- You should make lots of your own examples!

-- finishes with the value `unit` and the string "oh hai"
e1 :: Exp
e1 = parse [sexp|

((lambda (z)
  (output " hai"))
 (output "oh"))

|]

-- finishes with the value `unit` and the string "oh hai"
e2 :: Exp
e2 = parse [sexp| 

((lambda (fconcat)
 (output ((((lambda (x) x) 
            fconcat) 
           "oh") 
          " hai")))
 (lambda (x) 
  (lambda (y) 
   ((lambda (z) 
     (concat x y))
    unit))))

|]




-- The main function that is called when you 'runhaskell eval.hs'.
-- As is, it prints "oh hai"
--
-- You are welcome to change the main function all you like.  We will not use
-- it in grading.
main :: IO ()


-- This commented out main function will run e1 through your evaluator and
-- print the output.
-- main :: IO ()
main = putStrLn $ show $ eval e8 Map.empty

---------------------------------------------------
----- parsing s-expressions into our language -----
----- don't worry about understanding this --------
---------------------------------------------------
parse :: SExp -> Exp
parse   [sexp| unit |] = UnitLit
parse s@[sexp| lambda |] = error $ "bad 'lambda' expression: " ++ show s
parse s@[sexp| concat |] = error $ "bad 'concat' expression: " ++ show s
parse s@[sexp| output |] = error $ "bad 'output' expression: " ++ show s
parse   [sexp| @str:s |] = StringLit s
parse   [sexp| @sym:x |] = Var x
parse   [sexp| (lambda (@sym:x) @:e) |] = Lambda x (parse e)
parse s@[sexp| (lambda . @:_) |] = error $ "bad 'lambda' expression: " ++ show s
parse   [sexp| (concat @:e1 @:e2) |] = Concat (parse e1) (parse e2)
parse s@[sexp| (concat . @:_) =|] = error $ "bad 'concat' expression: " ++ show s
parse   [sexp| (output @:e) |] = Output (parse e)
parse s@[sexp| (output . @:_) |] = error $ "bad 'output' expression: " ++ show s
parse   [sexp| (@:e1 @:e2) |] = App (parse e1) (parse e2)
parse _ = error "could not parse s-expression into Exp"
---------------------------------------------------
