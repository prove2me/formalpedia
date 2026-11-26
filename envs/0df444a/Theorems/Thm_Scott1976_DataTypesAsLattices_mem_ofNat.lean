-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
-- name    : Scott1976.DataTypesAsLattices.mem_ofNat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:54:30.358874+00:00
-- url     : https://prove2.me/theorems/6d6376f9-61c3-53fa-9cc1-6256fa1c7380
-- title:
--   Data Types As Lattices: mem of Nat
-- statement:
--   The Data Types As Lattices construction uses the mem of Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L19-L19
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L19-L19

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.mem_ofNat {n k : ℕ} : k ∈ ofNat n ↔ k = n := by sorry
