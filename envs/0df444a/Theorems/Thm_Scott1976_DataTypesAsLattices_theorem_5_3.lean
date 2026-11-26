-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_5_3
-- name    : Scott1976.DataTypesAsLattices.theorem_5_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:02.714432+00:00
-- url     : https://prove2.me/theorems/cb98db42-3e20-5957-be32-f2ad23a7a72a
-- title:
--   Data Types As Lattices: theorem 5 3
-- statement:
--   **Scott 1976, Theorem 5.3 (The function space theorem for algebraic
--   lattices).** The function-space retract of two closures is a retract.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L150-L155
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L150-L155

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_5_3 {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsRetract (arrowR a b) := by sorry
