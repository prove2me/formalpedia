-- Prove2me | Theorems.Thm_SoficGroups_KunPositiveWordMidrankEnergy_sofic_action_squared_energy_inv
-- name    : SoficGroups.KunPositiveWordMidrankEnergy.sofic_action_squared_energy_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/2488e27b-f8e2-4895-9580-e46f996e2594
-- title:
--   SoficGroups.KunPositiveWordMidrankEnergy.sofic_action_squared_energy_inv
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

theorem SoficGroups.KunPositiveWordMidrankEnergy.sofic_action_squared_energy_inv
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (f : (n : ℕ) → Fin (A.model n).size → ℝ)
    (hf0 : ∀ n x, 0 ≤ f n x)
    (hf1 : ∀ n x, f n x ≤ 1)
    (g : G)
    (hg : Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action g) /
          (A.model n).size) atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        squaredPermutationEnergy (f n) ((A.model n).action (g⁻¹)) /
          (A.model n).size) atTop (𝓝 0) := by sorry
