-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_sum_ineq_d7f2075680f7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_sum_ineq_d7f2075680f7
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:24:18.988383+00:00
-- url     : https://prove2.me/theorems/a820e32d-73ac-4cb7-8ff3-5208b3f52347
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature log sum ineq d7f2075680f7: P2 M Ground Theory Heights  Heights Inter Regularized Curvature log sum ineq d7f2075680f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature log sum ineq d7f2075680f7 construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature log sum ineq d7f2075680f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L135-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L135-L149

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_sum_ineq_d7f2075680f7 {x x0 ε : ℝ} (hx : 0 < x) (hx0 : 0 < x0) (hε : 0 < ε) :
    Real.log (x0 + ε) - x0 / (x0 + ε) * Real.log x0 ≤
      Real.log (x + ε) - x0 / (x0 + ε) * Real.log x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«log_sum_ineq» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_sum_ineq_d7f2075680f7
