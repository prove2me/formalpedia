-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_11
-- name    : Scott1976.DataTypesAsLattices.eq_5_11
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:09.511228+00:00
-- url     : https://prove2.me/theorems/837edf68-3dc1-4e74-9f62-2ff3a1168322
-- title:
--   Data Types As Lattices: eq 5 11
-- statement:
--   **Scott 1976, (5.11).** Closures act as expansive maps.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L138-L146
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L138-L146

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_5_11 {a b u x : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    funOf u x ⊆ funOf b (funOf u (funOf a x)) := by sorry
