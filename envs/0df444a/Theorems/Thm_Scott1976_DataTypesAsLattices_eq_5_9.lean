-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_9
-- name    : Scott1976.DataTypesAsLattices.eq_5_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:45.642801+00:00
-- url     : https://prove2.me/theorems/2cd8965a-e6a0-546e-a954-af953f2b9ead
-- title:
--   Data Types As Lattices: eq 5 9
-- statement:
--   **Scott 1976, (5.9)–(5.10).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L57-L66
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L57-L66

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_5_9 (x y : Pomega) : squareFst (squarePair x y) = x := by sorry
