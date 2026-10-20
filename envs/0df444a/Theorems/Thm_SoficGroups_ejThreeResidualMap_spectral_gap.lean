-- Prove2me | Theorems.Thm_SoficGroups_ejThreeResidualMap_spectral_gap
-- name    : SoficGroups.ejThreeResidualMap_spectral_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/262585d7-e520-4c4e-8e68-56a4a6f37493
-- title:
--   SoficGroups.ejThreeResidualMap_spectral_gap
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

theorem SoficGroups.ejThreeResidualMap_spectral_gap (x : H) (ε : ℝ)
    (h01 : (1 - ε) *
      (‖ejResidualProjection (V 0) x‖ ^ 2 +
        ‖ejResidualProjection (V 1) x‖ ^ 2) ≤
      ‖ejResidualProjection (V 0) x +
        ejResidualProjection (V 1) x‖ ^ 2)
    (h12 : (1 - ε) *
      (‖ejResidualProjection (V 1) x‖ ^ 2 +
        ‖ejResidualProjection (V 2) x‖ ^ 2) ≤
      ‖ejResidualProjection (V 1) x +
        ejResidualProjection (V 2) x‖ ^ 2)
    (h20 : (1 - ε) *
      (‖ejResidualProjection (V 2) x‖ ^ 2 +
        ‖ejResidualProjection (V 0) x‖ ^ 2) ≤
      ‖ejResidualProjection (V 2) x +
        ejResidualProjection (V 0) x‖ ^ 2) :
    (1 - 2 * ε) * ejThreeResidualEnergy V x ≤
      ‖ejThreeResidualMap V x‖ ^ 2 := by sorry
