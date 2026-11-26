-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e_le
-- name    : Scott1976.DataTypesAsLattices.mem_e_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:05.357414+00:00
-- url     : https://prove2.me/theorems/e0541cec-9fd3-5d44-941c-ff0d192ca459
-- title:
--   Data Types As Lattices: mem e le
-- statement:
--   The Data Types As Lattices construction uses the mem e le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L56-L57
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L56-L57

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.mem_e_le {n k : ℕ} (h : k ∈ e n) : k ≤ n := by sorry
