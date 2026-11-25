-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_le_of_le_fa7336628a43
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_le_of_le_fa7336628a43
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:02:17.00733+00:00
-- url     : https://prove2.me/theorems/f9be3ddf-c1f7-4c24-ab41-e50ff8cd1b77
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi le of le fa7336628a43: P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi le of le fa7336628a43
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi le of le fa7336628a43 construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi le of le fa7336628a43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L69-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L69-L83

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_le_of_le_fa7336628a43 {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ} (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z)
    (hle : ∀ᶠ y in 𝓝 z, ψ y ≤ φ y) (heq : ψ z = φ z) (w : J → ℂ) :
    ReciprocityTheory.AnForm.levi ψ z w ≤ ReciprocityTheory.AnForm.levi φ z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«levi_le_of_le» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_le_of_le_fa7336628a43
