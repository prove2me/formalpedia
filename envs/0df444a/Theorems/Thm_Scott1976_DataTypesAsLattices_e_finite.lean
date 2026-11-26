-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_e_finite
-- name    : Scott1976.DataTypesAsLattices.e_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:52:46.651527+00:00
-- url     : https://prove2.me/theorems/b4929f98-7be8-5afa-941a-656e36137ed9
-- title:
--   Data Types As Lattices: e finite
-- statement:
--   The Data Types As Lattices construction uses the e finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L59-L61
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L59-L61

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.e_finite (n : ℕ) : (e n).Finite := by sorry
