-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
-- name    : Scott1976.DataTypesAsLattices.mem_e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:52:43.768349+00:00
-- url     : https://prove2.me/theorems/a8300a56-5554-440d-a813-660a8b949d66
-- title:
--   Data Types As Lattices: mem e
-- statement:
--   The Data Types As Lattices construction uses the mem e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L33-L33
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L33-L33

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.mem_e {n k : ℕ} : k ∈ e n ↔ n.testBit k := by sorry
