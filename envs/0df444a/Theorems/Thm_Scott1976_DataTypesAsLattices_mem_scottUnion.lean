-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion
-- name    : Scott1976.DataTypesAsLattices.mem_scottUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:06.839337+00:00
-- url     : https://prove2.me/theorems/7dd64195-362d-4fe6-b3f8-5073e98bc5f0
-- title:
--   Data Types As Lattices: mem scott Union
-- statement:
--   The Data Types As Lattices construction uses the mem scott Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L48-L55
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L48-L55

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.mem_scottUnion {f : Pomega → Pomega} {x : Pomega} {k : ℕ} :
    k ∈ scottUnion f x ↔ ∃ n, e n ⊆ x ∧ k ∈ f (e n) := by sorry
