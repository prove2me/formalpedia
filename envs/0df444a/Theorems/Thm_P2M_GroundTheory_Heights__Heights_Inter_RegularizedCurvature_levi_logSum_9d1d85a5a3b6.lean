-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_logSum_9d1d85a5a3b6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_logSum_9d1d85a5a3b6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:31:29.847803+00:00
-- url     : https://prove2.me/theorems/49ef6d90-2680-5e49-a05f-020f6a8ba7d5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi log Sum 9d1d85a5a3b6: P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi log Sum 9d1d85a5a3b6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi log Sum 9d1d85a5a3b6 construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi log Sum 9d1d85a5a3b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L153-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L153-L212

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_logSum_9d1d85a5a3b6 {h : (J → ℂ) → ℝ} {T : (J → ℂ) → ℂ} {Φ : (J → ℂ) → ℝ} {z : J → ℂ} {ε : ℝ}
    (hφ : ContDiffAt ℝ 2 (fun y => Real.log (h y)) z) (hpos : ∀ᶠ y in 𝓝 z, 0 < h y)
    (hT : AnalyticAt ℂ T z) (hε : 0 < ε) (hΦ : ContDiffAt ℝ 2 Φ z)
    (hform : ∀ y, Φ y = Real.log (h y) + Real.log ((‖T y‖ / h y) ^ 2 + ε) / 2) (w : J → ℂ) :
    ∃ μ : ℝ, 0 ≤ μ ∧ μ ≤ 1 ∧
      μ * ReciprocityTheory.AnForm.levi (fun y => Real.log (h y)) z w ≤ ReciprocityTheory.AnForm.levi Φ z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«levi_logSum» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_logSum_9d1d85a5a3b6
