-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_const_1f6796170df7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_const_1f6796170df7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:24.262886+00:00
-- url     : https://prove2.me/theorems/3d94784a-5b8f-42c6-b105-7778c1e56744
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi const 1f6796170df7: P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi const 1f6796170df7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi const 1f6796170df7 construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi const 1f6796170df7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L85-L86

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_const_1f6796170df7 (c : ℝ) (z w : J → ℂ) : ReciprocityTheory.AnForm.levi (fun _ : J → ℂ => c) z w = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«levi_const» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_const_1f6796170df7
