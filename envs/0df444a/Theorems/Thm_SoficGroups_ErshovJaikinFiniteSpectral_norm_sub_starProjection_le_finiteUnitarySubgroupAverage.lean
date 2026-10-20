-- Prove2me | Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_norm_sub_starProjection_le_finiteUnitarySubgroupAverage
-- name    : SoficGroups.ErshovJaikinFiniteSpectral.norm_sub_starProjection_le_finiteUnitarySubgroupAverage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/245723e0-0668-4250-bcad-8499c97129a0
-- title:
--   SoficGroups.ErshovJaikinFiniteSpectral.norm_sub_starProjection_le_finiteUnitarySubgroupAverage
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ErshovJaikinFiniteSpectral
open Filter Topology
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SoficGroups.ErshovJaikinFiniteSpectral.norm_sub_starProjection_le_finiteUnitarySubgroupAverage
    (π : SoficGroups.UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K]
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (x : H) (hmem : finiteUnitarySubgroupAverage π K x ∈ U) :
    ‖x - U.starProjection x‖ ≤
      ‖finiteUnitarySubgroupAverage π K x - x‖ := by sorry
