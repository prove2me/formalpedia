-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_5_6
-- name    : Scott1976.DataTypesAsLattices.theorem_5_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:16.298791+00:00
-- url     : https://prove2.me/theorems/898a94a1-e8ca-4ed7-b4b9-d484e971a85f
-- title:
--   Data Types As Lattices: theorem 5 6
-- statement:
--   **Scott 1976, Theorem 5.6 / (5.15).** The universe applied to `x` is
--   closed under `a` and contains `x`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L167-L172
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L167-L172

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_5_6 (a x : Pomega) :
    x ∪ funOf a (Vapply a x) ⊆ Vapply a x := by sorry
