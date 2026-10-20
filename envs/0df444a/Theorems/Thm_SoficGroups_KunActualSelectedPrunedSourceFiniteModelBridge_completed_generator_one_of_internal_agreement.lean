-- Prove2me | Theorems.Thm_SoficGroups_KunActualSelectedPrunedSourceFiniteModelBridge_completed_generator_one_of_internal_agreement
-- name    : SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge.completed_generator_one_of_internal_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/52a50841-17a1-4b9e-9467-ee29a4d5e9fe
-- title:
--   SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge.completed_generator_one_of_internal_agreement
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.KunActualSoficRootRadius
open scoped BigOperators Pointwise

theorem SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge.completed_generator_one_of_internal_agreement
    {G : Type} [Group G] (S : Finset G)
    {W : Type}
    (σ : ↥S → Equiv.Perm W) (Z : Finset W)
    (τ : ↥S → Equiv.Perm {x : W // x ∈ Z})
    (hagrees : ∀ i (x : W) (hx : x ∈ Z)
      (_hi : σ i x ∈ Z),
        ((τ i ⟨x, hx⟩ : {x : W // x ∈ Z}) : W) = σ i x)
    (hidentity : ∀ i : ↥S, (i : G) = 1 → σ i = 1)
    (i : ↥S) (hi : (i : G) = 1) : τ i = 1 := by sorry
