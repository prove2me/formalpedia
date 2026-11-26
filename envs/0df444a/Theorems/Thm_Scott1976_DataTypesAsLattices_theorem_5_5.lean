-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_5_5
-- name    : Scott1976.DataTypesAsLattices.theorem_5_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:30.022748+00:00
-- url     : https://prove2.me/theorems/369482f0-ca71-4d42-8ef0-b74cda90f5d8
-- title:
--   Data Types As Lattices: theorem 5 5
-- statement:
--   **Scott 1976, Theorem 5.5 / (5.18).** `V` fixes closures on values.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L198-L200
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L198-L200

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_5_5 {a : Pomega} (ha : IsClosure a) (x : Pomega) :
    Vapply a x ⊆ funOf a x ∧ Vapply a (Vapply a x) = Vapply a x := by sorry
