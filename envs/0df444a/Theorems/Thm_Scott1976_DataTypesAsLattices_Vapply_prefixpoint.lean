-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_Vapply_prefixpoint
-- name    : Scott1976.DataTypesAsLattices.Vapply_prefixpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:15.64413+00:00
-- url     : https://prove2.me/theorems/86d1455d-04e2-5b0e-84a6-d89a0dcf7f22
-- title:
--   Data Types As Lattices: Vapply prefixpoint
-- statement:
--   `V(a)(x)` is a prefixpoint of `y ↦ x ∪ a(y)`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L158-L163
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L158-L163

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.Vapply_prefixpoint (a x : Pomega) :
    x ⊆ Vapply a x ∧ funOf a (Vapply a x) ⊆ Vapply a x := by sorry
