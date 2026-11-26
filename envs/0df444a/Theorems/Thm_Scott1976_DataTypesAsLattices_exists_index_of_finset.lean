-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_exists_index_of_finset
-- name    : Scott1976.DataTypesAsLattices.exists_index_of_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:56.087646+00:00
-- url     : https://prove2.me/theorems/03232fa6-2948-5479-b95c-d70aa3b1c553
-- title:
--   Data Types As Lattices: exists index of finset
-- statement:
--   The Data Types As Lattices construction uses the exists index of finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L81-L95
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L81-L95

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.exists_index_of_finset (xs : ℕ → Pomega)
    (hmono : ∀ n, xs n ⊆ xs (n + 1))
    (s : Finset ℕ) (h : ∀ k ∈ s, ∃ n, k ∈ xs n) :
    ∃ N, (s : Set ℕ) ⊆ xs N := by sorry
