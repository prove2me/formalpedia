-- Prove2me | Theorems.Thm_SoficGroups_ejStarProjection_re_inner
-- name    : SoficGroups.ejStarProjection_re_inner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/c40e2541-1f4a-4766-a75d-ff8b57a8415b
-- title:
--   SoficGroups.ejStarProjection_re_inner
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

theorem SoficGroups.ejStarProjection_re_inner (W : Submodule ℂ H)
    [W.HasOrthogonalProjection] (x : H) :
    RCLike.re (inner ℂ (W.starProjection x) x) =
      ‖W.starProjection x‖ ^ 2 := by sorry
