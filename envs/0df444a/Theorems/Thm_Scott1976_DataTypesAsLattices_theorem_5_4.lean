-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_5_4
-- name    : Scott1976.DataTypesAsLattices.theorem_5_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:23.29053+00:00
-- url     : https://prove2.me/theorems/096631b1-d2c5-4260-914e-bee2565337fa
-- title:
--   Data Types As Lattices: theorem 5 4
-- statement:
--   **Scott 1976, Theorem 5.4 (product half).** The boxed product of two
--   closures is a retract of the same shape as `⊗`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L192-L195
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L192-L195

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_5_4 {a b : Pomega} (_ha : IsClosure a) (_hb : IsClosure b) :
    boxTensor a b = graph (fun u =>
      squarePair (funOf a (squareFst u)) (funOf b (squareSnd u))) := by sorry
