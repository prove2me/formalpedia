-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_17
-- name    : Scott1976.DataTypesAsLattices.eq_5_17
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:25.357456+00:00
-- url     : https://prove2.me/theorems/dd4ec240-2b50-5d5d-9c13-c435c6204dae
-- title:
--   Data Types As Lattices: eq 5 17
-- statement:
--   **Scott 1976, (5.17).** `V(a)` is idempotent.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L105-L112
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L105-L112

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_5_17 (a x : Pomega) : Vapply a (Vapply a x) = Vapply a x := by sorry
