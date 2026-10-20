-- Prove2me | Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_finiteUnitarySubgroupAverage_sub
-- name    : SoficGroups.ErshovJaikinFiniteSpectral.finiteUnitarySubgroupAverage_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/9bfa196e-45aa-492a-a309-07a6f183c484
-- title:
--   SoficGroups.ErshovJaikinFiniteSpectral.finiteUnitarySubgroupAverage_sub
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

theorem SoficGroups.ErshovJaikinFiniteSpectral.finiteUnitarySubgroupAverage_sub
    (π : SoficGroups.UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (x : H) :
    finiteUnitarySubgroupAverage π K x - x =
      (Fintype.card K : ℂ)⁻¹ •
        ∑ k : K, (π (k : G) x - x) := by sorry
