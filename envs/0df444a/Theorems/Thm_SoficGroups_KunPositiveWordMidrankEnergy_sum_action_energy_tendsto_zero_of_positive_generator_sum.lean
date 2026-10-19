-- Prove2me | Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_sum_action_energy_tendsto_zero_of_positive_generator_sum
-- name    : SoficGroups.KunPositiveWordMidrankEnergy.sum_action_energy_tendsto_zero_of_positive_generator_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/864fdd74-a92d-4ab2-8253-85f6cbbb3dca
-- title:
--   SoficGroups.KunPositiveWordMidrankEnergy.sum_action_energy_tendsto_zero_of_positive_generator_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunPositiveWordMidrankEnergy.sum_action_energy_tendsto_zero_of_positive_generator_sum
    {G ι : Type*} [Group G] [Fintype ι]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G)
    (hgenerate : Subgroup.closure (Set.range s) = ⊤)
    (f : (n : ℕ) → Fin (A.model n).size → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x)
    (hf1 : ∀ n x, f n x ≤ 1)
    (hpositive : Tendsto
      (fun n =>
        (∑ i : ι,
          squaredPermutationEnergy (f n)
            ((A.model n).action (s i))) /
          (A.model n).size) atTop (𝓝 0))
    (S : Finset G) :
    Tendsto
      (fun n =>
        (∑ g ∈ S,
          squaredPermutationEnergy (f n) ((A.model n).action g)) /
          (A.model n).size) atTop (𝓝 0) := by sorry
