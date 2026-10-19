-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedComponentMidrankVariation_normalized_permutationRealVariation_tendsto_zero_of_energy
-- name    : SoficGroups.KunCompletedComponentMidrankVariation.normalized_permutationRealVariation_tendsto_zero_of_energy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/ccab273d-ae52-4903-83f7-505bb44b59f0
-- title:
--   SoficGroups.KunCompletedComponentMidrankVariation.normalized_permutationRealVariation_tendsto_zero_of_energy
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

theorem SoficGroups.KunCompletedComponentMidrankVariation.normalized_permutationRealVariation_tendsto_zero_of_energy
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (ι : Type*) [Fintype ι]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (f : (n : ℕ) → V n → ℝ)
    (henergy : Tendsto
      (fun n =>
        (∑ i : ι, ∑ x : V n,
          (f n (σ n i x) - f n x) ^ 2) /
            (Fintype.card (V n) : ℝ))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        permutationRealVariation (σ n) (f n) /
          (Fintype.card (V n) : ℝ))
      atTop (nhds 0) := by sorry
