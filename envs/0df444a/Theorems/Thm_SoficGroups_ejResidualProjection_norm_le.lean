-- Prove2me | Theorems.Thm_SoficGroups_ejResidualProjection_norm_le
-- name    : SoficGroups.ejResidualProjection_norm_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/9b343a09-917f-4468-a40d-d1e33d6f3b75
-- title:
--   SoficGroups.ejResidualProjection_norm_le
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

theorem SoficGroups.ejResidualProjection_norm_le (i : Fin 3) (x : H) :
    ‖ejResidualProjection (V i) x‖ ≤ ‖x‖ := by sorry
