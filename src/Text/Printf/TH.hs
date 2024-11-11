-- simplified type-safe printf, implemented with TH

module Text.Printf.TH (sprintf, format, println) where

import Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Data.Typeable
import qualified Text.Printf

-- | Type-safe formatting, built on top of @'printf'@.
--
-- >>> :t [sprintf|Hello!|]
-- [sprintf|Hello!|] :: String
-- >>> :t [sprintf|Hello %s!|]
-- [sprintf|Hello %s!|] :: String -> String
-- >>> [sprintf|Hello %s!|] "world"
-- "Hello world!"
sprintf :: QuasiQuoter
sprintf = QuasiQuoter
    { quoteExp  = parsePrintf
    , quotePat  = error "quotePat not implemented for sprintf"
    , quoteType = error "quoteType not implemented for sprintf"
    , quoteDec  = error "quoteDec not implemented for sprintf"
    }

parsePrintf :: String -> Q Exp
parsePrintf pat = do
  type' <- genPrintfType pat
  pure $ SigE (AppE (VarE 'Text.Printf.printf) (LitE (StringL pat))) type'

genPrintfType :: (MonadFail m) => String -> m TH.Type
genPrintfType pat = do
  args <- argTypes pat
  pure $ foldr (AppT . AppT ArrowT . ConT) (ConT ''String) args

argTypes :: (MonadFail m) => String -> m [TH.Name]
argTypes ""  = pure []
argTypes "%" = fail "argument list ended prematurely"
argTypes ('%':c:cs) = do
  ty <- case c of
    's' -> pure ''String
    'd' -> pure ''Integer
    'f' -> pure ''Float
    o   -> fail $ "unrecognised specifier: |%" ++ o : "|"
  (ty :) <$> argTypes cs
argTypes (_:cs) = argTypes cs

-- | Inspired by Rust macro @format!@.
--
-- Use @{}@ as argument placeholders.
-- Any @'Typeable'@ and @'Show'@ arguments are acceptable.
-- String arguments will be substituted directly;
-- those of other types will be @'show'@ed.
--
-- >>> :t [format|Hello {}!|]
-- [format|Hello {}!|] :: (Show a, Typeable a) => a -> String
format :: QuasiQuoter
format = QuasiQuoter
  { quoteExp  = parseFormat
  , quotePat  = error "quotePat not implemented for format"
  , quoteType = error "quoteType not implemented for format"
  , quoteDec  = error "quoteDec not implemented for format"
  }

-- | Inspired by Rust macro @println!@.
--
-- Use @{}@ as argument placeholders.
-- Any @'Typeable'@ and @'Show'@ arguments are acceptable.
-- String arguments will be substituted directly;
-- those of other types will be @'show'@ed.
--
-- >>> :t [println|Hello {} {}! It's year {} now.|]
-- [println|Hello {} {}! It's year {} now.|]
--   :: (Show arg1, Typeable arg1, Show arg2, Typeable arg2, Show arg3,
--       Typeable arg3) =>
--      arg1 -> arg2 -> arg3 -> IO ()
-- >>> [println|Hello {} {}! It's year {} now.|] "Graydon" "Hoare" (2006 :: Int)
-- Hello Graydon Hoare! It's year 2006 now.
println :: QuasiQuoter
println = QuasiQuoter
  { quoteExp  = parsePrintln
  , quotePat  = error "quotePat not implemented for println"
  , quoteType = error "quoteType not implemented for println"
  , quoteDec  = error "quoteDec not implemented for println"
  }

parseFormat, parsePrintln :: String -> Q Exp
parseFormat pat = do
  argN <- countFmtArgs pat
  string <- [t|String|]
  type' <- genType argN string
  pure $ SigE (AppE (VarE 'format') (LitE (StringL pat))) type'

parsePrintln pat = do
  argN <- countFmtArgs pat
  io <- [t|IO ()|]
  type' <- genType argN io
  pure $ SigE (AppE (VarE 'println') (LitE (StringL pat))) type'

class PolyFmt r where
  format' :: String -> r

instance PolyFmt String where
  format' = id

instance (Show a, Typeable a, PolyFmt r) => PolyFmt (a -> r) where
  format' :: String -> a -> r
  format' pat arg = format' (go pat arg)
    where go :: String -> a -> String
          go "" _  = error "too many args"
          go ('{':'{':xs) arg = '{' : go xs arg
          go ('}':'}':xs) arg = '}' : go xs arg
          go ('{':'}':xs) arg = case cast arg of
            Just str -> str ++ xs
            Nothing  -> show arg ++ xs
          go ('{':_) _ = error "lonely brace"
          go ('}':_) _ = error "lonely brace"
          go (x:xs) arg = x : go xs arg

class PolyPrintln r where
  println' :: String -> r

instance PolyPrintln (IO ()) where
  println' = putStrLn

instance (Show a, Typeable a, PolyPrintln r) => PolyPrintln (a -> r) where
  println' :: String -> a -> r
  println' pat arg = println' (go pat arg)
    where go :: String -> a -> String
          go "" _  = error "too many args"
          go ('{':'{':xs) arg = '{' : go xs arg
          go ('}':'}':xs) arg = '}' : go xs arg
          go ('{':'}':xs) arg = case cast arg of
            Just str -> str ++ xs
            Nothing  -> show arg ++ xs
          go ('{':_) _ = error "lonely brace"
          go ('}':_) _ = error "lonely brace"
          go (x:xs) arg = x : go xs arg

countFmtArgs :: (MonadFail m, Num n) => String -> m n
countFmtArgs = \case
  "" -> pure 0
  ('{':'{':xs) -> countFmtArgs xs
  ('}':'}':xs) -> countFmtArgs xs
  ('{':'}':xs) -> (+1) <$> countFmtArgs xs
  ('{':_) -> fail "lonely brace"
  ('}':_) -> fail "lonely brace"
  (x:xs) -> countFmtArgs xs

genType :: (Num n, Ord n, MonadFail m, Quote m) => n -> TH.Type -> m TH.Type
genType n _ | n < 0 = fail "wtf?"
genType 0 ret = pure $ ForallT [] [] ret
genType n ret = do
  ForallT oldSpecs oldCxt oldType <- genType (n - 1) ret
  a <- newName "arg"
  let newSpecs = PlainTV a SpecifiedSpec : oldSpecs
      newCxt = AppT (ConT ''Show) (VarT a) : AppT (ConT ''Typeable) (VarT a) : oldCxt
      newType = AppT (AppT ArrowT (VarT a)) oldType
  pure $ ForallT newSpecs newCxt newType
