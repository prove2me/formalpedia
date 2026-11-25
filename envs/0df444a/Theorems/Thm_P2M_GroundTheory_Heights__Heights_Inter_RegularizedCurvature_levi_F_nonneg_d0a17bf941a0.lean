-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_F_nonneg_d0a17bf941a0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_F_nonneg_d0a17bf941a0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:31:21.855295+00:00
-- url     : https://prove2.me/theorems/34ebc571-7268-562b-903e-8c55f55ebd41
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi F nonneg d0a17bf941a0: P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi F nonneg d0a17bf941a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi F nonneg d0a17bf941a0 construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature levi F nonneg d0a17bf941a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L252-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L252-L258

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_F_nonneg_d0a17bf941a0 {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K)
    (w : (Σ k, ι k) → ℂ) : 0 ≤ ReciprocityTheory.AnForm.levi (F k) z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«levi_F_nonneg» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_F_nonneg_d0a17bf941a0
