-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_1
-- name    : Scott1976.DataTypesAsLattices.eq_5_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:32.214891+00:00
-- url     : https://prove2.me/theorems/7469460c-2fe2-5505-82b7-f2f4c83c7080
-- title:
--   Data Types As Lattices: eq 5 1
-- statement:
--   **Scott 1976, (5.1).** `u ⊆ λx. u(x)`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L26-L27
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L26-L27

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_5_1 (u : Pomega) : u ⊆ graph (fun x => funOf u x) := by sorry
