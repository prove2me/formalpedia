-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_isPotential_24ccbbf0e1d3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_res_isPotential_24ccbbf0e1d3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:52:51.419457+00:00
-- url     : https://prove2.me/theorems/f62c3221-0db3-46fc-a8b7-8487a15cd841
-- title:
--   P2 M Ground Theory Heights  Heights Inter res is Potential 24ccbbf0e1d3: P2 M Ground Theory Heights  Heights Inter res is Potential 24ccbbf0e1d3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter res is Potential 24ccbbf0e1d3 construction uses the P2 M Ground Theory Heights  Heights Inter res is Potential 24ccbbf0e1d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L88-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L88-L162

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UnitChartOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (GroundTheory.Heights₂.Heights.NumbersDVR.MRing ι ℂ)} {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_res_isPotential_24ccbbf0e1d3 (R : Res ι P e) {L : HLine ι} (hL : IsSmoothMetric P L) :
    IsPotential R.atlas (R.pot (logH L)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«res_isPotential» := P2M_GroundTheory_Heights__Heights_Inter_res_isPotential_24ccbbf0e1d3
