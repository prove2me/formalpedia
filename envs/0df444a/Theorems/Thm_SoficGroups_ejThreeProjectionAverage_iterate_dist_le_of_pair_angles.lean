-- Prove2me | Theorems.Thm_SoficGroups_ejThreeProjectionAverage_iterate_dist_le_of_pair_angles
-- name    : SoficGroups.ejThreeProjectionAverage_iterate_dist_le_of_pair_angles
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/1221aad9-9eae-45d1-b2ae-8d792bdba07a
-- title:
--   SoficGroups.ejThreeProjectionAverage_iterate_dist_le_of_pair_angles
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]

theorem SoficGroups.ejThreeProjectionAverage_iterate_dist_le_of_pair_angles
    [∀ i j : Fin 3, (V i ⊓ V j).HasOrthogonalProjection]
    (c : ℝ) (hc : 0 ≤ c) (hchalf : c < (1 / 2 : ℝ))
    (hangle : ∀ (i j : Fin 3) (u v : H),
      u ∈ V i → u ∈ (V i ⊓ V j)ᗮ →
      v ∈ V j → v ∈ (V i ⊓ V j)ᗮ →
        ‖inner ℂ u v‖ ≤ c * ‖u‖ * ‖v‖)
    (x : H) (n : ℕ) :
    dist (((ejThreeProjectionAverage V : H → H)^[n]) x)
        (((ejThreeProjectionAverage V : H → H)^[n + 1]) x) ≤
      Real.sqrt (ejThreeResidualEnergy V x / 3) *
        (1 - (1 - 2 * c) / 6) ^ n := by sorry
