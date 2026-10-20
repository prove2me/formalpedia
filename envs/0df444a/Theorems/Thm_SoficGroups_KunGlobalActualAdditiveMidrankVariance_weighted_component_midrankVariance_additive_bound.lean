-- Prove2me | Theorems.Thm_SoficGroups_KunGlobalActualAdditiveMidrankVariance_weighted_component_midrankVariance_additive_bound
-- name    : SoficGroups.KunGlobalActualAdditiveMidrankVariance.weighted_component_midrankVariance_additive_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/e75709a6-b132-474d-9db0-d58708a89483
-- title:
--   SoficGroups.KunGlobalActualAdditiveMidrankVariance.weighted_component_midrankVariance_additive_bound
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunGlobalActualAdditiveMidrankVariance
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunGlobalActualAdditiveMidrankVariance.weighted_component_midrankVariance_additive_bound
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (P : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V)
    (τ : (C : Finset V) → ι → Equiv.Perm {x : V // x ∈ C})
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hτ : ∀ C ∈ P.parts, ∀ i (x : V)
      (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ C i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (hexpand : ∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (SoficGroups.boundary σ E : ℝ))
    (b : V → ℤ) :
    2 * γ *
        (∑ C ∈ P.parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C b)) ≤
      SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation
        σ (SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank P b) +
        5 * (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) := by sorry
