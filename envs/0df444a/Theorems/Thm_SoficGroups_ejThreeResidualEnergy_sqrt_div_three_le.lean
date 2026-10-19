-- Prove2me | Theorems.Thm_SoficGroups_ejThreeResidualEnergy_sqrt_div_three_le
-- name    : SoficGroups.ejThreeResidualEnergy_sqrt_div_three_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/c934ea7c-6bcb-41f5-a5b3-a7b88b9a4c27
-- title:
--   SoficGroups.ejThreeResidualEnergy_sqrt_div_three_le
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

theorem SoficGroups.ejThreeResidualEnergy_sqrt_div_three_le
    (x : H) (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ i : Fin 3,
      ‖ejResidualProjection (V i) x‖ ≤ T) :
    Real.sqrt (ejThreeResidualEnergy V x / 3) ≤ T := by sorry
