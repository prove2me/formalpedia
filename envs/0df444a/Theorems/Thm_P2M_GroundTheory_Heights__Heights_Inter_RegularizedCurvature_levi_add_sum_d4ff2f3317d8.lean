-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_add_sum_d4ff2f3317d8
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_add_sum_d4ff2f3317d8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:24:28.512323+00:00
-- url     : https://prove2.me/theorems/32175835-f372-43b7-a6a2-1a548fbf6dc4
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi add sum d4ff2f3317d8: P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi add sum d4ff2f3317d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi add sum d4ff2f3317d8 construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi add sum d4ff2f3317d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L266-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L266-L281

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_add_sum_d4ff2f3317d8 {K : Type} {z : J → ℂ} (g : (J → ℂ) → ℝ) (f : K → (J → ℂ) → ℝ) (c : K → ℝ)
    (hg : ContDiffAt ℝ 2 g z) (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (w : J → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => g y + ∑ k ∈ s, c k * f k y) z ∧
      ReciprocityTheory.AnForm.levi (fun y => g y + ∑ k ∈ s, c k * f k y) z w =
        ReciprocityTheory.AnForm.levi g z w + ∑ k ∈ s, c k * ReciprocityTheory.AnForm.levi (f k) z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«levi_add_sum» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_add_sum_d4ff2f3317d8
