-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_5_5_values
-- name    : Scott1976.DataTypesAsLattices.theorem_5_5_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:45.912934+00:00
-- url     : https://prove2.me/theorems/f91102e4-43d2-5102-a885-0b81dc0d91f7
-- title:
--   Data Types As Lattices: theorem 5 5 values
-- statement:
--   **Scott 1976, Theorem 5.5 (partial).** `V(a)` is always a closure of `x`,
--   and `V` fixes exactly the closure operations in the sense of (5.18) on values.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L116-L118
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L116-L118

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_5_5_values (a x : Pomega) :
    x ⊆ Vapply a x ∧ Vapply a (Vapply a x) = Vapply a x := by sorry
