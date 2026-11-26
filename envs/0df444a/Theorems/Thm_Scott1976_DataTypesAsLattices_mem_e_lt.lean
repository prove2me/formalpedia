-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e_lt
-- name    : Scott1976.DataTypesAsLattices.mem_e_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:50.759329+00:00
-- url     : https://prove2.me/theorems/686d2931-5599-47c9-8438-58551a521b86
-- title:
--   Data Types As Lattices: mem e lt
-- statement:
--   The Data Types As Lattices construction uses the mem e lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L449-L453
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L449-L453

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.mem_e_lt {n k : ℕ} (h : k ∈ e n) : k < n := by sorry
