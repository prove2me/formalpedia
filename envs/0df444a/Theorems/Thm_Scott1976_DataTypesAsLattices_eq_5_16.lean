-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_16
-- name    : Scott1976.DataTypesAsLattices.eq_5_16
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:32.833475+00:00
-- url     : https://prove2.me/theorems/8e6e9564-5648-45c0-9b92-c3e7cc376956
-- title:
--   Data Types As Lattices: eq 5 16
-- statement:
--   **Scott 1976, (5.16).** `x ⊆ V(a)(x)`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L100-L102
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L100-L102

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_5_16 (a x : Pomega) : x ⊆ Vapply a x := by sorry
