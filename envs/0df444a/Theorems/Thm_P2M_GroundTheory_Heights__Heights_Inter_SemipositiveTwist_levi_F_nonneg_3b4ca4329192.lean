-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_F_nonneg_3b4ca4329192
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_F_nonneg_3b4ca4329192
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:27:59.67394+00:00
-- url     : https://prove2.me/theorems/52683951-3e49-5697-a7fb-86ef56333a39
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi F nonneg 3b4ca4329192: P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi F nonneg 3b4ca4329192
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi F nonneg 3b4ca4329192 construction uses the P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi F nonneg 3b4ca4329192 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L60-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.Inter.SemipositiveTwist
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_F_nonneg_3b4ca4329192 {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K)
    (w : (Σ k, ι k) → ℂ) : 0 ≤ ReciprocityTheory.AnForm.levi (F k) z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemipositiveTwist».«levi_F_nonneg» := P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_F_nonneg_3b4ca4329192
