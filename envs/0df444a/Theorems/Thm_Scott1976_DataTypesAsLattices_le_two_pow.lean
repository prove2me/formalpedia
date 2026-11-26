-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_le_two_pow
-- name    : Scott1976.DataTypesAsLattices.le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:10.02077+00:00
-- url     : https://prove2.me/theorems/a55479e1-1616-5084-9cfc-622b848e4a60
-- title:
--   Data Types As Lattices: le two pow
-- statement:
--   The Data Types As Lattices construction uses the le two pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L46-L54
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L46-L54

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.le_two_pow (k : ℕ) : k ≤ 2 ^ k := by sorry
