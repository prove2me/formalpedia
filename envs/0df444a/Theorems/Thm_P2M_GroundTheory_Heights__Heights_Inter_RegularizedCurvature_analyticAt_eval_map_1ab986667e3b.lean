-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_analyticAt_eval_map_1ab986667e3b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_analyticAt_eval_map_1ab986667e3b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:23:43.092313+00:00
-- url     : https://prove2.me/theorems/15628f15-1cff-4d02-bf8c-7fc90ef5f714
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature analytic At eval map 1ab986667e3b: P2 M Ground Theory Heights  Heights Inter Regularized Curvature analytic At eval map 1ab986667e3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature analytic At eval map 1ab986667e3b construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature analytic At eval map 1ab986667e3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L94-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
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
open GroundTheory.Heights₂.Heights.Inter.RegularizedCurvature
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_analyticAt_eval_map_1ab986667e3b (p : MvPolynomial J ℤ) (z : J → ℂ) :
    AnalyticAt ℂ (fun y : J → ℂ => MvPolynomial.eval y (MvPolynomial.map (Int.castRingHom ℂ) p)) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«analyticAt_eval_map» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_analyticAt_eval_map_1ab986667e3b
