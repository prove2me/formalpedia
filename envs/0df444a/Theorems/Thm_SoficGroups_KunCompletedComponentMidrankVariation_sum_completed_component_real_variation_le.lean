-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedComponentMidrankVariation_sum_completed_component_real_variation_le
-- name    : SoficGroups.KunCompletedComponentMidrankVariation.sum_completed_component_real_variation_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/36b89001-8a45-4e00-9b89-d1beee726edf
-- title:
--   SoficGroups.KunCompletedComponentMidrankVariation.sum_completed_component_real_variation_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedComponentMidrankVariation
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunCompletedComponentMidrankVariation.sum_completed_component_real_variation_le
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (P : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V)
    (τ : (C : Finset V) → ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ C ∈ P.parts, ∀ i (x : V)
      (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ C i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (f : V → ℝ)
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    (∑ C ∈ P.parts,
      permutationRealVariation (τ C) (fun x => f (x : V))) ≤
      permutationRealVariation σ f +
        ∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ) := by sorry
