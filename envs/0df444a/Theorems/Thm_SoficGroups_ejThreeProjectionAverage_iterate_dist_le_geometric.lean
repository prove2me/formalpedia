-- Prove2me | Theorems.Thm_SoficGroups_ejThreeProjectionAverage_iterate_dist_le_geometric
-- name    : SoficGroups.ejThreeProjectionAverage_iterate_dist_le_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/fdfaa92d-569e-43a1-a564-e38d47e54bcb
-- title:
--   SoficGroups.ejThreeProjectionAverage_iterate_dist_le_geometric
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

theorem SoficGroups.ejThreeProjectionAverage_iterate_dist_le_geometric
    (δ : ℝ) (hδ : δ ≤ 3)
    (hgap : ∀ x : H,
      δ * ejThreeResidualEnergy V x ≤ ‖ejThreeResidualMap V x‖ ^ 2)
    (x : H) (n : ℕ) :
    dist (((ejThreeProjectionAverage V : H → H)^[n]) x)
        (((ejThreeProjectionAverage V : H → H)^[n + 1]) x) ≤
      Real.sqrt (ejThreeResidualEnergy V x / 3) *
        (1 - δ / 6) ^ n := by sorry
