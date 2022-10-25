{-# language DeriveAnyClass             #-}
{-# language DeriveDataTypeable         #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase                 #-}
{-# language NamedFieldPuns             #-}
{-# language StandaloneDeriving         #-}
{-# language TemplateHaskell            #-}
module Main where

import           Data.Functor ((<&>))
import           Data.List (transpose)
import qualified Data.Map as Map
import           Data.Traversable (for)
import           Data.SBV
import           Data.SBV.Internals (SMTModel(..), CV(..), CVal(..))
import           Data.SBV.List hiding ((!!), elem)
import           Data.SBV.Tools.BoundedList

data Elem = Monster | Chest | Empty | Wall
mkSymbolicEnumeration ''Elem

monster, chest, empty, wall :: SBV Elem
monster = literal Monster
chest = literal Chest
empty = literal Empty
wall = literal Wall

type Row = [Elem]
type Position = (Int8, Int8)

data Constraints = Constraints {
  monsters :: [Position],
  chestPos :: Position,
  rowCounts :: [Int8],
  colCounts :: [Int8]
}

type Board = [[SBV Elem]]

testBoard :: Constraints
testBoard = Constraints {
  monsters = [
    (2, 2),
    (6, 0),
    (7, 3),
    (7, 5),
    (7, 7)
  ],
  chestPos = (2, 6),
  rowCounts = [5, 2, 2, 1, 5, 3, 2, 5],
  colCounts = [4, 2, 5, 0, 6, 2, 4, 2]
}

foldBools :: [SBool] -> SBool
foldBools = foldr (.&&) sTrue

checkBoard :: Constraints -> Board -> SBool
checkBoard (Constraints {monsters, chestPos, rowCounts, colCounts}) board =
  foldBools
    [ constrainCells board chestPos monsters
    , checkRows board rowCounts
    , checkRows (transpose board) colCounts
    , checkMonsters board monsters
    , checkChest board chestPos
    ]

-- Each monster / chest has to remain one. Each other cell has to be empty or a
-- wall.
constrainCells :: Board -> Position -> [Position] -> SBool
constrainCells board chestPos monsters =
  foldBools $ [0..7] <&> \row ->
    foldBools $ [0..7] <&> \col ->
      let cell = board !! row !! col
          pos = (fromIntegral row, fromIntegral col)
      in
      if pos == chestPos then cell .== chest
      else if pos `elem` monsters then cell .== monster
      else cell .== empty .|| cell .== wall

-- Check the number of walls in each row
checkRows :: Board -> [Int8] -> SBool
checkRows rows counts = foldBools $
  [0..7] <&> \i -> checkWallCount (rows !! i) (counts !! i)

checkWallCount :: [SBV Elem] -> Int8 -> SBool
checkWallCount elems n =
  sum (map (oneIf . (.== literal Wall)) elems) .== literal n

-- A monster must be at a dead end, ie surrounded on three sides by either a
-- wall or edge, and an empty position on the other side
checkMonster :: Board -> Position -> SBool
checkMonster board (y, x) = wallCount .== literal 3
  where
    x' = fromIntegral x
    y' = fromIntegral y
    wallCount :: SInt8
    wallCount = sum $ map oneIf $
      [ literal y .== 0 .|| (board !! (y'-1) !! x' .== wall)
      , literal y .== 7 .|| (board !! (y'+1) !! x' .== wall)
      , literal x .== 0 .|| (board !! y' !! (x'-1) .== wall)
      , literal x .== 7 .|| (board !! y' !! (x'+1) .== wall)
      ]

checkMonsters :: Board -> [Position] -> SBool
checkMonsters board monsters = foldBools $ checkMonster board <$> monsters

-- A chest must be surrounded on all sides by an empty position
checkChest :: Board -> Position -> SBool
checkChest board (y, x) =
  foldBools $ [x-1..x+1] <&> \x' ->
    foldBools $ [y-1..y+1] <&> \y' ->
      let expected = if x' == x && y' == y then chest else empty in
      board !! fromIntegral y' !! fromIntegral x' .== expected

unconstrainedBoard :: Symbolic Board
unconstrainedBoard = for [0..7] $ \i -> for [0..7] $ \j -> free (show (i, j))

showModel :: SMTModel -> String
showModel (SMTModel _ _ assocs _) =
  let assocs' = Map.fromList assocs
      showCV (CV _ cvVal) = case cvVal of
        CUserSort (Just i, _) -> case i of
          0 -> 'm'
          1 -> 'c'
          2 -> ' '
          3 -> '#'
        _ -> '?'
  in
  unlines $
    [0..7] <&> \row ->
      [0..7] <&> \col ->
        showCV $ assocs' Map.! (show (row, col))

main :: IO ()
main = do
  SatResult result <- sat $ checkBoard testBoard <$> unconstrainedBoard
  let output =
        case result of
          Satisfiable _config model -> showModel model
          _ -> "Unsat or something"
  putStrLn output
