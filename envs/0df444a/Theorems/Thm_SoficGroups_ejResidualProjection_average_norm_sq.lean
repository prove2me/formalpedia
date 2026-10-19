-- Prove2me | Theorems.Thm_SoficGroups_ejResidualProjection_average_norm_sq
-- name    : SoficGroups.ejResidualProjection_average_norm_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/3eff81ee-1ee1-4d73-990d-1b05b7962f45
-- title:
--   SoficGroups.ejResidualProjection_average_norm_sq
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

theorem SoficGroups.ejResidualProjection_average_norm_sq
    (W : Submodule ℂ H) [W.HasOrthogonalProjection]
    (x z : H) :
    ‖ejResidualProjection W (x - (3 : ℂ)⁻¹ • z)‖ ^ 2 =
      ‖ejResidualProjection W x‖ ^ 2 -
        (2 / 3 : ℝ) * RCLike.re
          (inner ℂ (ejResidualProjection W x)
            (ejResidualProjection W z)) +
        (1 / 9 : ℝ) * ‖ejResidualProjection W z‖ ^ 2 := by sorry
