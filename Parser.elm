module Parser where

import String(uncons, cons)
import List(foldr, zip, any, concat, map, (++))
import Char(isDigit)

-- Implementation of http://www.cs.nott.ac.uk/~gmh/pearl.pdf
-- by Graham Hutton and Erik Meijer

data Parser a = Parser (String -> [(a, String)])

item : Parser Char
item = Parser 
       (\cs -> case uncons cs of
                 Just x -> [x]
                 _      -> [] )

parse (Parser p) = p


-- LAWS: 
-- returnP a >>= f = f a
-- p >>= returnP = p
-- p >>= (\a -> (f a >>= g)) = (p >>= (\a -> f a)) >>= g

-- AKA return
returnP : a -> Parser a
returnP a = Parser (\cs -> [(a, cs)])

-- Exactly the the monadic bind operator for Parsers
(>>=) : Parser a -> (a -> Parser b) -> Parser b
p >>= f = Parser 
  (\cs -> 
    let acs  = parse p cs
    in  concat <| map (\(a, cs') -> parse (f a) cs') acs )

(>>) : Parser a -> Parser b -> Parser b
p >> f = p >>= \_ -> f

-- LAWS:
-- zeroP <+> p = p
-- p <+> zeroP = p
-- p <+> (q <+> r) = (p <+> q) <+> r
-- 
-- zeroP >>= f = zeroP
-- p >>= always zeroP = zeroP
-- (p <+> q) >>= f = (p >>= f) <+> (q >>= f)
-- p >>= (\a -> f a <+> g a) = (p >>= f) <+> (p >>= g)

-- AKA zero from MonadZero
zeroP : Parser a
zeroP = Parser (\_ -> [])

-- AKA ++ from MonadPlus
-- may return many results
(<+>) : Parser a -> Parser a -> Parser a
p <+> q = Parser (\cs -> parse p cs ++ parse q cs)

-- +++ from the paper, returns at most one result
-- all laws for <+> hold for +++
(+++) : Parser a -> Parser a -> Parser a
p +++ q = Parser 
  (\cs -> 
    case parse (p <+> q) cs of
      (x::xs) -> [x]
      _       -> [] )

-- Satisfy Parse a character satisfying predicate `p`
sat : (Char -> Bool) -> Parser Char
sat p = item >>= \c -> if p c then returnP c else zeroP

-- Parse a single character
char : Char -> Parser Char
char c = sat (\c' -> c' == c)

-- Parse a specific String
string : String -> Parser String
string xs = case uncons xs of
  Nothing -> returnP ""
  Just (c, cs) -> char c >> string cs >> returnP (cons c cs)

-- Parse repeated applications of a parser p (permits 0 applications)
-- Note: Since String /= [Char] in Elm,
--       many (char c) will not produce Strings.
many : Parser a -> Parser [a]
many p = many1 p <+> returnP []

-- Parse repeated applications of a parser p (1 or more) 
many1 : Parser a -> Parser [a]
many1 p = p >>= \x -> many p >>= \xs -> returnP (x::xs)

-- Parse repeated applications of a parser p, 
-- separated by applications of a parser sep whose results are tossed.
sepBy : Parser a -> Parser b -> Parser [a]
p `sepBy` sep = p `sepBy1` sep <+> returnP []

-- Same, with 1 or more applications of sep
sepBy1 : Parser a -> Parser b -> Parser [a]
p `sepBy1` sep = p >>= \x -> many (sep >> p) >>= \xs -> returnP (x::xs)

-- Parse repeated applications of p, separated by applications of a
-- Parser `op`, whose result value is an operator that is assumed to 
-- associate to the left, used to combine the results from 
-- each application of `p`.
chainl : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = (p `chainl1` op) <+> returnP a

chainl1 : Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op =
  let rest a =  ( op >>= \f -> 
                  p  >>= \b ->
                  rest (f a b) ) 
                <+> returnP a
  in p >>= \a -> rest a

-- Same as above, but the `op` associates to the right
chainr : Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainr p op a= (p `chainr1` op) <+> returnP a

chainr1 : Parser a -> Parser (a -> a -> a) -> Parser a
p `chainr1` op =
  let scan   = p >>= \a -> rest a
      rest a = op   >>= \f ->
               scan >>= \b ->
               returnP (f a b)
  in scan

-- Since this isn't a part of the standard library, define it
isSpace : Char -> Bool
isSpace c = any (\c' -> c' == c) ['\r', '\n', '\t', ' ']

-- Workaround, since String /= [Char] in Elm
parseStr : Parser [Char] -> Parser String
parseStr f = f >>= \xs -> returnP (foldr cons "" xs)

-- Parse a string of whitespace
space : Parser String
space = parseStr <| many (sat isSpace)

-- Parse some token, trimming space
token : Parser a -> Parser a
token p = p >>= \a -> space >> returnP a

-- Parse a symbolic token
symb : String -> Parser String
symb cs = token (string cs)

-- Parse a token, removing leading space
apply : Parser a -> String -> [(a, String)]
apply p = parse (space >> p)

-- This could use a nicer syntax...
p : Parser (Char, Char)
p = item >>= \c -> item >> item >>= \d -> returnP (c, d)

-- Example at the end of the paper:
lookup : a -> [(a, b)] -> Maybe b
lookup a xs' = case xs' of
  []           -> Nothing
  ((x, y)::xs) -> if x == a then Just y else lookup a xs 

ord : Char -> Int
ord c = case lookup c (zip ['0'..'9'] [0..9]) of
  Just x  -> x
  Nothing -> -1 -- don't know how to throw an error?

expr = term   `chainl1` addOp
term = factor `chainl1` mulOp

factor = digit +++ (symb "(" >> expr >>= \n -> symb ")" >> returnP n)

digit = token (sat isDigit) >>= \x -> returnP (ord x)

addOp : Parser (Int -> Int -> Int)
addOp = ( symb "+" >> returnP (+) ) +++ ( symb "-" >> returnP (-) )

mulOp : Parser (Int -> Int -> Int)
mulOp = ( symb "*" >> returnP (*) ) +++ ( symb "/" >> returnP (div) )

-- errors for some reason
-- example = parse expr "1+1"

-- example main function
main = asText <| parse (space >> string "hell") "     hello!"
