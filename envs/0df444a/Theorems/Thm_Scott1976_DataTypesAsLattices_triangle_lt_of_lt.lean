-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_triangle_lt_of_lt
-- name    : Scott1976.DataTypesAsLattices.triangle_lt_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:29.648825+00:00
-- url     : https://prove2.me/theorems/9e5236d8-73b8-42bc-9d54-cfa3defcb80a
-- title:
--   Data Types As Lattices: triangle lt of lt
-- statement:
--   The Data Types As Lattices construction uses the triangle lt of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L120-L125
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L120-L125

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.triangle_lt_of_lt {a b : ℕ} (h : a < b) : triangle a < triangle b := by sorry
