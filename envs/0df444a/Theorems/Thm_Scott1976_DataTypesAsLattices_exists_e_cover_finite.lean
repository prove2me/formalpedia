-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_exists_e_cover_finite
-- name    : Scott1976.DataTypesAsLattices.exists_e_cover_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:58.05316+00:00
-- url     : https://prove2.me/theorems/cd840ff4-90c9-49b1-807d-51ffdf164de2
-- title:
--   Data Types As Lattices: exists e cover finite
-- statement:
--   If each element of a finite set is realized at some `e n ⊆ x`, the
--   bitwise-OR of those codes realizes the whole finite set (using monotonicity).
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L67-L83
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L67-L83

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.exists_e_cover_finite {f : Pomega → Pomega} (hf : IsScottContinuous f)
    {x : Pomega} (s : Finset ℕ)
    (h : ∀ k ∈ s, ∃ n, e n ⊆ x ∧ k ∈ f (e n)) :
    ∃ N, e N ⊆ x ∧ (s : Set ℕ) ⊆ f (e N) := by sorry
