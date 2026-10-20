-- Prove2me | Theorems.Thm_SoficGroups_ejThreeProjectionAverage_dist_sq
-- name    : SoficGroups.ejThreeProjectionAverage_dist_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/e97e193d-b248-4f8a-82ee-ba7b353af9b9
-- title:
--   SoficGroups.ejThreeProjectionAverage_dist_sq
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

theorem SoficGroups.ejThreeProjectionAverage_dist_sq (x : H) :
    dist x (ejThreeProjectionAverage V x) ^ 2 =
      (1 / 9 : ℝ) * ‖ejThreeResidualMap V x‖ ^ 2 := by sorry
