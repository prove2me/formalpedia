-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_res_continuousOn_lift_e6623d19a860
-- name    : P2M_GroundTheory_Heights__Heights_Inter_res_continuousOn_lift_e6623d19a860
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:52:55.038409+00:00
-- url     : https://prove2.me/theorems/31ae83f8-7160-485d-9e88-12942b740fe6
-- title:
--   P2 M Ground Theory Heights  Heights Inter res continuous On lift e6623d19a860: P2 M Ground Theory Heights  Heights Inter res continuous On lift e6623d19a860
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter res continuous On lift e6623d19a860 construction uses the P2 M Ground Theory Heights  Heights Inter res continuous On lift e6623d19a860 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/UnitChartOperator.lean#L76-L86

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

theorem P2M_GroundTheory_Heights__Heights_Inter_res_continuousOn_lift_e6623d19a860 (R : Res ι P e) (x : R.R.M) (p : Σ k, ι k) :
    ContinuousOn (fun z => R.liftAt x z p) (R.R.src (R.idx x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«res_continuousOn_lift» := P2M_GroundTheory_Heights__Heights_Inter_res_continuousOn_lift_e6623d19a860
