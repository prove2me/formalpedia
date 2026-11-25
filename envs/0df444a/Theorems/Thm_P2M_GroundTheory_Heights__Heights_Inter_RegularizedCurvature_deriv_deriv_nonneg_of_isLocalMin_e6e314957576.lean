-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_deriv_deriv_nonneg_of_isLocalMin_e6e314957576
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_deriv_deriv_nonneg_of_isLocalMin_e6e314957576
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:28:18.227175+00:00
-- url     : https://prove2.me/theorems/2572e097-2414-4006-9f20-721ff588291e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature deriv deriv nonneg of is Local Min e6e314957576: P2 M Ground Theory Heights  Heights Inter Regularized Curvature deriv deriv nonneg of i
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature deriv deriv nonneg of is Local Min e6e314957576 construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature deriv deriv nonneg of is Local Min e6e314957576 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L21-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L21-L32

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_deriv_deriv_nonneg_of_isLocalMin_e6e314957576 {g : ℝ → ℝ} (hg : IsLocalMin g 0) (hc : ContinuousAt g 0) :
    0 ≤ deriv (deriv g) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«deriv_deriv_nonneg_of_isLocalMin» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_deriv_deriv_nonneg_of_isLocalMin_e6e314957576
