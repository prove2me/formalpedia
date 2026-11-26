-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_5_1
-- name    : Scott1976.DataTypesAsLattices.theorem_5_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:52.081938+00:00
-- url     : https://prove2.me/theorems/8806cc3d-f1d2-5c6a-b473-e63ea65c2e64
-- title:
--   Data Types As Lattices: theorem 5 1
-- statement:
--   **Scott 1976, Theorem 5.1.** Images `a(e n)` are isolated fixed points
--   of a closure (they are fixed because `a` is a retract).
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L133-L135
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L133-L135

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_5_1 {a : Pomega} (ha : IsClosure a) (n : ℕ) :
    typed (funOf a (e n)) a := by sorry
