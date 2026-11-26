-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_pair_eq_triangle
-- name    : Scott1976.DataTypesAsLattices.pair_eq_triangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:12.261195+00:00
-- url     : https://prove2.me/theorems/536bd56b-8339-4bfa-baeb-ebb6f8cf81cf
-- title:
--   Data Types As Lattices: pair eq triangle
-- statement:
--   The Data Types As Lattices construction uses the pair eq triangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L101-L101
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L101-L101

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.pair_eq_triangle (n m : ℕ) : pair n m = triangle (n + m) + m := by sorry
