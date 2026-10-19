-- Prove2me | Theorems.Thm_SoficGroups_KunGlobalActualAdditiveMidrankVariance_weighted_component_midrankVariance_tendsto_zero_of_source_half_expansion
-- name    : SoficGroups.KunGlobalActualAdditiveMidrankVariance.weighted_component_midrankVariance_tendsto_zero_of_source_half_expansion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/a92ca572-b162-4437-a2d1-0888d94d67a0
-- title:
--   SoficGroups.KunGlobalActualAdditiveMidrankVariance.weighted_component_midrankVariance_tendsto_zero_of_source_half_expansion
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

theorem SoficGroups.KunGlobalActualAdditiveMidrankVariance.weighted_component_midrankVariance_tendsto_zero_of_source_half_expansion
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (ι : Type*) [Fintype ι]
    (P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (b : (n : ℕ) → V n → ℤ)
    (γ : ℝ) (hγ : 0 < γ)
    (hexpand : ∀ n C, C ∈ (P n).parts → ∀ E : Finset (V n),
      E ⊆ C → 2 * E.card ≤ C.card →
        γ * (E.card : ℝ) ≤ (SoficGroups.boundary (σ n) E : ℝ))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            (Fintype.card (V n) : ℝ))
      atTop (nhds 0))
    (henergy : Tendsto
      (fun n =>
        (∑ i : ι, ∑ x : V n,
          (SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank
            (P n) (b n) (σ n i x) -
           SoficGroups.MidrankPermutationEnergy.partitionVertexMidrank
            (P n) (b n) x) ^ 2) /
              (Fintype.card (V n) : ℝ))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C (b n))) /
                (Fintype.card (V n) : ℝ))
      atTop (nhds 0) := by sorry
