-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedComponentMidrankVariation_completed_component_real_variation_le
-- name    : SoficGroups.KunCompletedComponentMidrankVariation.completed_component_real_variation_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/8fc44416-dc75-4b84-90f0-ea2d0dc75165
-- title:
--   SoficGroups.KunCompletedComponentMidrankVariation.completed_component_real_variation_le
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

theorem SoficGroups.KunCompletedComponentMidrankVariation.completed_component_real_variation_le
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V)
    (C : Finset V)
    (τ : ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ i (x : V) (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (f : V → ℝ)
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    permutationRealVariation τ (fun x => f (x : V)) ≤
      (∑ i : ι, ∑ x ∈ C, |f (σ i x) - f x|) +
        (SoficGroups.boundary σ C : ℝ) := by sorry
