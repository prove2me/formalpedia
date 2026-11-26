-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_18
-- name    : Scott1976.DataTypesAsLattices.eq_5_18
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:15.574957+00:00
-- url     : https://prove2.me/theorems/33dd04b7-aa59-45fd-8c3b-e1d8686e0b14
-- title:
--   Data Types As Lattices: eq 5 18
-- statement:
--   **Scott 1976, (5.18).** If `a` is already a closure, then `V(a)(x) = a(x)`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L121-L129
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L121-L129

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_5_18 {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x ⊆ funOf a x := by sorry
