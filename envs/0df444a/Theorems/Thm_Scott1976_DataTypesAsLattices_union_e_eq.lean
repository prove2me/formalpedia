-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_union_e_eq
-- name    : Scott1976.DataTypesAsLattices.union_e_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:24.311051+00:00
-- url     : https://prove2.me/theorems/971cdc68-8f68-4f6c-b195-c6c6b56c4eda
-- title:
--   Data Types As Lattices: union e eq
-- statement:
--   The Data Types As Lattices construction uses the union e eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L73-L81
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L73-L81

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.union_e_eq (x : Pomega) : (⋃ n, eBelow x n) = x := by sorry
