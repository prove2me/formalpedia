-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_two_pow_le_of_testBit
-- name    : Scott1976.DataTypesAsLattices.two_pow_le_of_testBit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:04.824774+00:00
-- url     : https://prove2.me/theorems/d7f85fb5-8a7a-42ff-be14-73cb78791fe9
-- title:
--   Data Types As Lattices: two pow le of test Bit
-- statement:
--   The Data Types As Lattices construction uses the two pow le of test Bit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L39-L44
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L39-L44

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.two_pow_le_of_testBit {n k : ℕ} (h : n.testBit k) : 2 ^ k ≤ n := by sorry
