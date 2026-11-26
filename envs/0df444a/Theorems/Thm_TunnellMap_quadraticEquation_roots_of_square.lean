-- Prove2me | Theorems.Thm_TunnellMap_quadraticEquation_roots_of_square
-- name    : TunnellMap.quadraticEquation_roots_of_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:40.290327+00:00
-- url     : https://prove2.me/theorems/5dc7bf12-3004-52c1-a6f1-92a3a8d167cd
-- title:
--   Tunnell Map: quadratic Equation roots of square
-- statement:
--   The Tunnell Map construction uses the quadratic Equation roots of square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L45-L62
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuadraticRoots.lean#L45-L62

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.quadraticEquation_roots_of_square {α c d s a : ℤ}
    (hα : α ≠ 0) (hs : s ^ 2 = quadraticHalfDiscriminant α c d) :
    quadraticEquation α c d a ↔
      (α * a = -c + s ∨ α * a = -c - s) := by sorry
