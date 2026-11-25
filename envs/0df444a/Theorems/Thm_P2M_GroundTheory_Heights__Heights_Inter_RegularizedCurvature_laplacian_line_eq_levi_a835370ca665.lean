-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_laplacian_line_eq_levi_a835370ca665
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_laplacian_line_eq_levi_a835370ca665
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:45.265028+00:00
-- url     : https://prove2.me/theorems/58813557-4475-5dc8-a796-d4fb44b82bee
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature laplacian line eq levi a835370ca665: P2 M Ground Theory Heights  Heights Inter Regularized Curvature laplacian line eq levi a835370ca665
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature laplacian line eq levi a835370ca665 construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature laplacian line eq levi a835370ca665 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L283-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L283-L304

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_laplacian_line_eq_levi_a835370ca665 {φ : (J → ℂ) → ℝ} {z : J → ℂ} (hφ : ContDiffAt ℝ 2 φ z) (v : J → ℂ) :
    Δ (fun t : ℂ => φ (z + t • v)) 0 = 4 * ReciprocityTheory.AnForm.levi φ z v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«laplacian_line_eq_levi» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_laplacian_line_eq_levi_a835370ca665
