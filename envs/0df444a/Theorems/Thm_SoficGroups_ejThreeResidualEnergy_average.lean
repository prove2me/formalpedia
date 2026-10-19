-- Prove2me | Theorems.Thm_SoficGroups_ejThreeResidualEnergy_average
-- name    : SoficGroups.ejThreeResidualEnergy_average
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/aac12cde-f8dc-4874-861d-8500a4e46602
-- title:
--   SoficGroups.ejThreeResidualEnergy_average
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

theorem SoficGroups.ejThreeResidualEnergy_average (x : H) :
    ejThreeResidualEnergy V (ejThreeProjectionAverage V x) =
      ejThreeResidualEnergy V x -
        (2 / 3 : ℝ) * ‖ejThreeResidualMap V x‖ ^ 2 +
        (1 / 9 : ℝ) *
          ejThreeResidualEnergy V (ejThreeResidualMap V x) := by sorry
