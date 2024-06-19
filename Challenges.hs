{-# LANGUAGE DeriveGeneric #-}
-- comp2209 Functional Programming Challenges
-- (c) University of Southampton 2021
-- Skeleton code to be updated with your solutions
-- The dummy functions here simply return an arbitrary value that is usually wrong

-- DO NOT MODIFY THE FOLLOWING LINES OF CODE
module Challenges (Atoms,Interactions,Pos,EdgePos,Side(..),Marking(..),
                   LamExpr(..),LetExpr(..),CLExpr(..),
                   calcBBInteractions,
                   solveBB,
                   prettyPrint,
                   parseLet,
                   clTransform,
                   innerRedn1,outerRedn1,innerCLRedn1,outerCLRedn1,compareInnerOuter
                   )
where


-- Import standard library and parsing definitions from Hutton 2016, Chapter 13
import Data.Char
import Parsing
import Control.Monad
import Data.List
import GHC.Generics (Generic,Generic1)
import Control.DeepSeq
-- Your other imports here
import Text.Read
import Data.Maybe

instance NFData CLExpr
instance NFData LetExpr
instance NFData LamExpr
instance NFData Marking
instance NFData Side

-- Challenge 1
-- Calculate Interactions in the Black Box

type Atoms = [ Pos ]
type Interactions = [  ( EdgePos , Marking )  ]
type Pos = (Int, Int)   -- top left is (1,1) , bottom right is (N,N) where N is size of grid
type EdgePos = ( Side , Int ) -- int range is 1 to N where N is size of grid

data Side = North | East | South | West
            deriving (Show, Eq, Ord)

data Marking =  Absorb | Reflect | Path EdgePos
                deriving (Show, Eq)

data Direction = Left | Right | Top | Bottom
                deriving (Show, Eq)

calcBBInteractions :: Int -> Atoms -> Interactions
calcBBInteractions 0 _ = []
calcBBInteractions _ [] = []
calcBBInteractions i xs = checkRay (sortBy sortSnd[(x, y) | x <- [1..i], y <- [North, South, East, West]]) i xs

--Calculate for a single ray
checkRay :: [(Int, Side)] -> Int -> Atoms -> Interactions
checkRay [] _  _ = []
checkRay (x:xs) size atoms | snd x == North = fixReflection $ deflect1 (fst x) size [((North, fst x), South)] (North, South) atoms (0, 0) ++ checkRay xs size atoms
                           | snd x == East = fixReflection $ deflect1 (fst x) size [((East, fst x), West)] (East, West) atoms (0, 0) ++ checkRay xs size atoms
                           | snd x == South = fixReflection $ deflect1 (fst x) size [((South, fst x), North)] (South, North) atoms (0, 0) ++ checkRay xs size atoms
                           | snd x == West = fixReflection $ deflect1 (fst x) size [((West, fst x), East)] (West, East) atoms (0, 0) ++ checkRay xs size atoms


findAtom :: Eq a1 => a1 -> [a2] -> (a2 -> a1) -> [a2]
findAtom x xs f = [y | y <- xs, f y == x ]

--If the entry is the same as the exit, make it a reflection
fixReflection :: [(EdgePos, Marking)] -> [(EdgePos, Marking)]
fixReflection [] = []
fixReflection [((x, n),Path (y, i))] | x == y, n == i = [((x, n), Reflect)]
                                     | otherwise = [((x, n),Path (y, i))]
fixReflection xs = xs

deflect1 :: Int -> Int -> [((Side, Int), Side)] -> (Side, Side) -> Atoms -> Pos -> Interactions
deflect1 i size steps (start, end) atoms lastAtom | start == East, lastAtom /= (0, 0) = east $ reverse $ sortBy sortFst([x | x <- removeItem lastAtom (findAtom (i - 1) atoms snd ++ findAtom (i + 1) atoms snd), fst x < fst lastAtom])
                                                  | start == North, lastAtom /= (0, 0) = north $ sortBy sortSnd([x | x <- removeItem lastAtom (findAtom (i - 1) atoms fst ++ findAtom (i + 1) atoms fst), snd x > snd lastAtom])
                                                  | start == West, lastAtom /= (0, 0) = west $ sortBy sortFst([x | x <- removeItem lastAtom (findAtom (i - 1) atoms snd ++ findAtom (i + 1) atoms snd), fst x > fst lastAtom])
                                                  | start == South, lastAtom /= (0, 0) = south $ reverse $ sortBy sortSnd([x | x <- removeItem lastAtom (findAtom (i - 1) atoms fst ++ findAtom (i + 1) atoms fst), snd x < snd lastAtom])
                                                  | start == East = east $ reverse $ sortBy sortFst(removeItem lastAtom (findAtom (i - 1) atoms snd ++ findAtom (i + 1) atoms snd))
                                                  | start == North = north $ sortBy sortSnd(removeItem lastAtom (findAtom (i - 1) atoms fst ++ findAtom (i + 1) atoms fst))
                                                  | start == West = west $ sortBy sortFst(removeItem lastAtom (findAtom (i - 1) atoms snd ++ findAtom (i + 1) atoms snd))
                                                  | start == South = south $ reverse $ sortBy sortSnd(removeItem lastAtom (findAtom (i - 1) atoms fst ++ findAtom (i + 1) atoms fst))

     where east sortedAtoms | not $ null $ findAtom i atoms snd, null sortedAtoms || fst (head sortedAtoms) < fst (head $ findAtom i atoms snd) = [((fst $ fst $ head steps, snd $ fst $ head steps), Absorb)]
                            | null sortedAtoms = [((fst $ fst $ head steps, snd $ fst $ head steps), Path (snd $ last steps, i))]
                            | fst (head sortedAtoms) == size = [((fst $ fst $ head steps, snd $ fst $ head steps), Reflect)]
                            | length sortedAtoms > 1, fst (head sortedAtoms) == fst (head(tail sortedAtoms)), snd (head sortedAtoms) - snd (head(tail sortedAtoms)) == 2 || snd (head sortedAtoms) - snd (head(tail sortedAtoms)) == -2 = deflect1 i size (steps ++ [((West, i), East)]) (West, East) atoms (head sortedAtoms)
                            | snd (head sortedAtoms) < i = deflect1 (fst (head sortedAtoms) + 1) size (steps ++ [((North, fst (head sortedAtoms) + 1), South)]) (North, South) atoms (head sortedAtoms)
                            | snd (head sortedAtoms) > i = deflect1 (fst (head sortedAtoms) + 1) size (steps ++ [((South, fst (head sortedAtoms) + 1), North)]) (South, North) atoms (head sortedAtoms)

           north sortedAtoms | not $ null $ findAtom i atoms fst, null sortedAtoms || snd (head sortedAtoms) > snd (head $ findAtom i atoms fst) = [((fst $ fst $ head steps, snd $ fst $ head steps), Absorb)]
                             | null sortedAtoms = [((fst $ fst $ head steps, snd $ fst $ head steps), Path (snd $ last steps, i))]
                             | snd (head sortedAtoms) == 1 = [((fst $ fst $ head steps, snd $ fst $ head steps), Reflect)]
                             | length sortedAtoms > 1, snd (head sortedAtoms) == snd (head(tail sortedAtoms)), fst (head sortedAtoms) - fst (head(tail sortedAtoms)) == 2 || fst (head sortedAtoms) - fst (head(tail sortedAtoms)) == -2 = deflect1 i size (steps ++ [((South, i), North)]) (South, North) atoms (head sortedAtoms)
                             | fst (head sortedAtoms) < i = deflect1 (snd (head sortedAtoms) - 1) size (steps ++ [((West, snd (head sortedAtoms) - 1), East)]) (West, East) atoms (head sortedAtoms)
                             | fst (head sortedAtoms) > i = deflect1 (snd (head sortedAtoms) - 1) size (steps ++ [((East, snd (head sortedAtoms) - 1), West)]) (East, West) atoms (head sortedAtoms)

           west sortedAtoms | not $ null $ findAtom i atoms snd, null sortedAtoms || fst (head sortedAtoms) > fst (head $ findAtom i atoms snd) = [((fst $ fst $ head steps, snd $ fst $ head steps), Absorb)]
                            | null sortedAtoms = [((fst $ fst $ head steps, snd $ fst $ head steps), Path (snd $ last steps, i))]
                            | fst (head sortedAtoms) == 1 = [((fst $ fst $ head steps, snd $ fst $ head steps), Reflect)]
                            | length sortedAtoms > 1, fst (head sortedAtoms) == fst (head(tail sortedAtoms)), snd (head sortedAtoms) - snd (head(tail sortedAtoms)) == 2 || snd (head sortedAtoms) - snd (head(tail sortedAtoms)) == -2 = deflect1 i size (steps ++ [((East, i), West)]) (East, West) atoms (head sortedAtoms)
                            | snd (head sortedAtoms) < i = deflect1 (fst (head sortedAtoms) - 1) size (steps ++ [((North, fst (head sortedAtoms) - 1), South)]) (North, South) atoms (head sortedAtoms)
                            | snd (head sortedAtoms) > i = deflect1 (fst (head sortedAtoms) - 1) size (steps ++ [((South, fst (head sortedAtoms) - 1), North)]) (South, North) atoms (head sortedAtoms)

           south sortedAtoms | not $ null $ findAtom i atoms fst, null sortedAtoms || snd (head sortedAtoms) < snd (head $ findAtom i atoms fst) = [((fst $ fst $ head steps, snd $ fst $ head steps), Absorb)]
                             | null sortedAtoms = [((fst $ fst $ head steps, snd $ fst $ head steps), Path (snd $ last steps, i))]
                             | snd (head sortedAtoms) == size = [((fst $ fst $ head steps, snd $ fst $ head steps), Reflect)]
                             | length sortedAtoms > 1, snd (head sortedAtoms) == snd (head(tail sortedAtoms)), fst (head sortedAtoms) - fst (head(tail sortedAtoms)) == 2 || fst (head sortedAtoms) - fst (head(tail sortedAtoms)) == -2 = deflect1 i size (steps ++ [((North, i), South)]) (North, South) atoms (head sortedAtoms)
                             | fst (head sortedAtoms) < i = deflect1 (snd (head sortedAtoms) + 1) size (steps ++ [((West, snd (head sortedAtoms) + 1), East)]) (West, East) atoms (head sortedAtoms)
                             | fst (head sortedAtoms) > i = deflect1 (snd (head sortedAtoms) + 1) size (steps ++ [((East, snd (head sortedAtoms) + 1), West)]) (East, West) atoms (head sortedAtoms)

removeItem _ []                 = []
removeItem x (y:ys) | x == y    = removeItem x ys
                    | otherwise = y : removeItem x ys

sortFst (a1, b1) (a2, b2)
    | a1 < a2 = LT
    | a1 > a2 = GT
    | a1 == a2 = compare a1 a2

sortSnd (a1, b1) (a2, b2)
    | b1 < b2 = LT
    | b1 > b2 = GT
    | b1 == b2 = compare b1 b2

-- Challenge 2
-- Solve a Black Box
solveBB :: Int -> Interactions -> Atoms
solveBB _ [] = []
solveBB _ _ = []

-- Challenge 3
-- Pretty Printing Lambda with Scott Numerals

data LamExpr =  LamApp LamExpr LamExpr  |  LamAbs Int LamExpr  |  LamVar Int
                deriving (Eq, Show, Read)

prettyPrint :: LamExpr -> String
prettyPrint x = removeWhiteSpace $ checkSE x 0

pretty2 :: LamExpr -> String
pretty2 (LamVar num) = "x" ++ show num
pretty2 (LamApp (LamAbs num x) (LamApp y z)) | isNothing (test $ checkSE (LamAbs num x) 0) = "(" ++ checkSE (LamAbs num x) 0 ++ ") " ++ "(" ++ checkSE(LamApp y z) 0 ++ ")"
                                             | otherwise = checkSE (LamAbs num x) 0 ++ " " ++ "(" ++ checkSE(LamApp y z) 0 ++ ")"
pretty2 (LamApp (LamAbs num x) y ) | isNothing (test $ checkSE (LamAbs num x) 0) = "(" ++ checkSE (LamAbs num x) 0 ++ ") " ++ checkSE y 0
                                   | otherwise = checkSE (LamAbs num x) 0 ++ " " ++ checkSE y 0
pretty2 (LamApp (LamApp a b) (LamApp y z)) | isNothing (test $ checkSE (LamApp a b) 0), not $ checkAbs b = checkSE (LamApp a b) 0 ++ " (" ++ checkSE (LamApp y z) 0 ++ ")"
                                           | checkAbs b = "(" ++ checkSE (LamApp a b) 0 ++ ") " ++ "(" ++ checkSE (LamApp y z) 0 ++ ")"
                                           | otherwise = checkSE (LamApp a b) 0 ++ " " ++ checkSE (LamApp y z) 0
    where checkAbs (LamAbs num y) = True
          checkAbs _ = False
pretty2 (LamApp (LamApp x y) z) | isNothing (test $ checkSE x 0), checkAbs y = "(" ++ checkSE (LamApp x y) 0 ++ ") " ++ checkSE z 0
                                | otherwise = checkSE (LamApp x y) 0 ++ " " ++ checkSE z 0
    where checkAbs (LamAbs num y) = True
          checkAbs _ = False
pretty2 (LamApp x (LamApp y z)) | isNothing (test $ checkSE x 0) = checkSE x 0 ++ " (" ++ checkSE (LamApp y z) 0 ++ ")"
                                | otherwise = checkSE x 0 ++ " " ++ checkSE (LamApp y z) 0
pretty2 (LamApp x y) = checkSE x 0 ++ " " ++ checkSE y 0
pretty2 (LamAbs num y) = "\\x" ++ show num ++ " -> " ++ checkSE y 0

test s = readMaybe s :: Maybe Int

--Remove white spaces
removeWhiteSpace [] = []
removeWhiteSpace xs | head xs == ' ' = removeWhiteSpace $ tail xs
                    | last xs == ' ' = removeWhiteSpace $ init xs
                    | otherwise = xs

--Check for scott numerals
checkSE :: LamExpr -> Int -> String
checkSE e n = check e e n
    where check (LamAbs x (LamAbs y (LamVar z))) start n | x == z    = show n
                                                         | otherwise = pretty2 start
          check (LamAbs x (LamAbs y (LamApp (LamVar z) e))) start n | y == z = check e start (n + 1)
                                                                    | otherwise = pretty2 start
          check e start n = pretty2 start

-- Challenge 4 
-- Parsing Let Expressions

data LetExpr =  LetApp LetExpr LetExpr | LetDef [([Int], LetExpr)] LetExpr |
                LetFun Int | LetVar Int | LetNum Int
                deriving (Show, Eq)

parseLet :: String -> Maybe LetExpr
parseLet []  = Nothing
parseLet s | null expr = Nothing
           | otherwise = Just $ fst $ head expr
    where expr = parse parseExpr s

parseNum :: Parser LetExpr
parseNum = do n <- nat
              return (LetNum n)

parseVar :: Parser LetExpr
parseVar = do x <- char 'x'
              n <- nat
              return (LetVar n)

--Get the value of Var
getVarValue :: Parser Int
getVarValue = do char 'x'
                 n <- nat
                 space
                 return n

parseFun :: Parser LetExpr
parseFun = do f <- char 'f'
              n <- nat
              space
              return (LetFun n)

--Get the value of a function "f1 = 1"
parseFunNum :: Parser Int
parseFunNum = do char 'f'
                 n <- nat
                 space
                 return n

parseVarList :: Parser [Int]
parseVarList = do n <- some getVarValue
                  return n

parseApp :: Parser LetExpr
parseApp = do first <- parseParen <|> parseNum <|> parseVar <|> parseFun <|> parseLetExpr 
              space
              second <- parseParen <|> parseNum <|> parseVar <|> parseFun <|> parseLetExpr 
              space
              more <- many (parseApp <|> parseNum <|> parseVar <|> parseFun <|> parseLetExpr) 
              if null more
              then return (LetApp first second)
              else return (LetApp (LetApp first second) (head more))

parseExpr :: Parser LetExpr
parseExpr = do x <- parseApp <|> parseParen <|> parseLetExpr <|> parseNum <|> parseVar <|> parseFun
               return x

--Handle parentheses
parseParen :: Parser LetExpr
parseParen = do space
                char '('
                expr <- parseExpr
                char ')'
                space
                return expr

parseEqn :: Parser [([Int], LetExpr)]
parseEqn = do fNum <- parseFunNum
              vars <- parseVarList
              space
              eq <- char '='
              space
              eqVars <- parseExpr --replace with var
              return [(fNum : vars, eqVars)]

parseEqnList :: Parser [([Int], LetExpr)]
parseEqnList = do f <- parseEqn
                  char ';'
                  space
                  tail <- parseEqnList
                  return (f ++ tail)
               <|> parseEqn

parseLetExpr :: Parser LetExpr
parseLetExpr = do l <- string "let"
                  space
                  eqs <- parseEqnList
                  space
                  string "in"
                  space
                  expr <- parseExpr
                  return (LetDef eqs expr)

-- Challenge 5
-- Encode lambda terms as combinators 

data TransExpr =  App TransExpr TransExpr  |  Abs Int TransExpr  |  Var Int | ST | KT  | IT
                  deriving (Show,Read,Eq)

data CLExpr = S | K  | I | CLVar Int | CLApp CLExpr CLExpr
              deriving (Show,Read,Eq)

clTransform :: LamExpr -> CLExpr
clTransform expr = convertTransToCL $ trans (convertLamToTrans expr)

--Convert from the transition data type to CLExpr
convertTransToCL :: TransExpr -> CLExpr
convertTransToCL ST = S
convertTransToCL KT = K
convertTransToCL IT = I
convertTransToCL (Var num) = CLVar num
convertTransToCL (App e1 e2) = CLApp (convertTransToCL e1) (convertTransToCL e2)

--Convert LamExpr to the transition data type
convertLamToTrans :: LamExpr -> TransExpr
convertLamToTrans (LamVar x) = Var x
convertLamToTrans (LamAbs n e) = Abs n (convertLamToTrans e)
convertLamToTrans (LamApp x y) = App (convertLamToTrans x) (convertLamToTrans y)

trans :: TransExpr -> TransExpr
trans ST = ST
trans IT = IT
trans KT = KT
trans (Var x) = Var x -- 1
trans (App x y) = App (trans x) (trans y) -- 2
trans (Abs x (Var y)) | x == y = IT -- 4
trans (Abs x (Abs y e)) | free x e = trans (Abs x (trans (Abs y e))) -- 5
trans (Abs x (App a b)) | free x a || free x b = App (App ST (trans (Abs x a))) (trans (Abs x b)) -- 6
trans (Abs x e) | not $ free x e = App KT (trans e) -- 3

-- Adapted from Lecture 38 - Implementing Beta reduction
free :: Int -> TransExpr -> Bool
free x (Var y) = x == y
free x (Abs y e) | x == y = False
free x (Abs y e) | x /= y = free x e
free x (App y z) = free x y || free x z
free _ _ = False

-- Challenge 6
-- Compare Innermost and Outermost Reduction for Lambda and Combinators 

-- Adapted from Lecture 38 - Implementing Beta reduction
freeCH6 :: Int -> LamExpr -> Bool
freeCH6 x (LamVar y) = x == y
freeCH6 x (LamAbs y e) | x == y = False
freeCH6 x (LamAbs y e) | x /= y = freeCH6 x e
freeCH6 x (LamApp y z) = freeCH6 x y || freeCH6 x z
freeCH6 _ _ = False

-- Adapted from Lecture 38 - Implementing Beta reduction
subst :: LamExpr -> Int -> LamExpr -> LamExpr
subst (LamVar x) y e | x == y = e
subst (LamVar x) y e | x /= y = LamVar x
subst (LamAbs x e1) y e | x /= y && not (freeCH6 x e) = LamAbs x (subst e1 y e)
subst (LamAbs x e1) y e | x /=y && freeCH6 x e = let x1 = rename x e1 in
                          subst (LamAbs x1 (subst e1 x (LamVar x1))) y e
subst (LamAbs x e1) y e | x == y = LamAbs x e1
subst (LamApp e1 e2) y e = LamApp (subst e1 y e) (subst e2 y e)

-- Adapted from Lecture 38 - Implementing Beta reduction
rename :: Int -> LamExpr -> Int
rename x e | freeCH6 (x + 1) e = rename (x + 1) e
           | otherwise = x + 1

-- Adapted from Lecture 38 - Implementing Beta reduction
eval1cbn :: LamExpr -> LamExpr
eval1cbn (LamAbs x e) = LamAbs x e
eval1cbn (LamApp (LamAbs x e1) e2) = subst e1 x e2
eval1cbn (LamApp e1 e2) = LamApp (eval1cbn e1) e2
eval1cbn expr = expr 

-- Adapted from Lecture 39 - Implementing Evaluation
eval1cbv :: LamExpr -> LamExpr
eval1cbv (LamAbs x e) = LamAbs x e
eval1cbv (LamApp (LamAbs x e1) e@(LamAbs y e2)) = subst e1 x e
eval1cbv (LamApp e@(LamAbs x e1) e2) = LamApp e (eval1cbv e2)
eval1cbv (LamApp e1 e2) = LamApp (eval1cbv e1) e2
eval1cbv expr = expr 



clRedOut :: CLExpr -> CLExpr
clRedOut (CLApp I x) = x
clRedOut (CLApp (CLApp K x) y) = x
clRedOut (CLApp (CLApp S (CLApp x y)) z) = CLApp (CLApp x y) (CLApp y z)
clRedOut (CLApp x y) = CLApp (clRedOut x) y
clRedOut expr = expr

clRedIn :: CLExpr -> CLExpr
clRedIn (CLApp I x) = x
clRedIn (CLApp (CLApp K x) y) = x
clRedIn (CLApp (CLApp S (CLApp x y)) z) = CLApp (clRedIn (CLApp x y)) (CLApp y z)
clRedIn (CLApp x y) = CLApp (clRedOut x) y
clRedIn expr = expr


extractFromJust (Just e) = e

countOuterLam expr acc func | acc == 0, isNothing $ func expr = 0
                            | isJust $ func expr = countOuterLam (extractFromJust $ outerRedn1 expr) (acc + 1) func
                            | otherwise = acc

outerRedn1 :: LamExpr -> Maybe LamExpr
outerRedn1 expr | eval1cbn expr == expr = Nothing
                | otherwise = Just $ eval1cbn expr

innerRedn1 :: LamExpr -> Maybe LamExpr
innerRedn1 expr | eval1cbv expr == expr = Nothing
                | otherwise = Just $ eval1cbv expr

outerCLRedn1 :: CLExpr -> Maybe CLExpr
outerCLRedn1 expr | clRedOut expr == expr = Nothing
                  | otherwise = Just $ clRedOut expr

innerCLRedn1 :: CLExpr -> Maybe CLExpr
innerCLRedn1 expr | clRedIn expr == expr = Nothing
                  | otherwise = Just $ clRedIn expr

compareInnerOuter :: LamExpr -> Int -> (Maybe Int,Maybe Int,Maybe Int,Maybe Int)
compareInnerOuter _ _ = (Just 0, Just 0, Just 0, Just 0)


