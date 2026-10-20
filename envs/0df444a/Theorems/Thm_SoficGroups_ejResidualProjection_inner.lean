-- Prove2me | Theorems.Thm_SoficGroups_ejResidualProjection_inner
-- name    : SoficGroups.ejResidualProjection_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/c1e3e381-947b-4cbd-80ba-11902dc5cf3b
-- title:
--   SoficGroups.ejResidualProjection_inner
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

theorem SoficGroups.ejResidualProjection_inner (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] (x y : H) :
    inner ℂ (ejResidualProjection V x) y =
      inner ℂ x (ejResidualProjection V y) := by sorry
