-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_triangle_le_pair
-- name    : Scott1976.DataTypesAsLattices.triangle_le_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:15.553868+00:00
-- url     : https://prove2.me/theorems/f02fbbca-2d5e-5cfc-afe5-a6c8427f6c29
-- title:
--   Data Types As Lattices: triangle le pair
-- statement:
--   The Data Types As Lattices construction uses the triangle le pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L127-L132
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L127-L132

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.triangle_le_pair (n m : ℕ) :
    triangle (n + m) ≤ pair n m ∧ pair n m < triangle (n + m + 1) := by sorry
