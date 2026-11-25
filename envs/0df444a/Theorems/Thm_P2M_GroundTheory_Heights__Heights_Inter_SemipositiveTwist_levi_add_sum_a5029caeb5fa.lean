-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_add_sum_a5029caeb5fa
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_add_sum_a5029caeb5fa
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:23.858062+00:00
-- url     : https://prove2.me/theorems/251c9906-6710-4f0f-bcef-050c9394b61b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi add sum a5029caeb5fa: P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi add sum a5029caeb5fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi add sum a5029caeb5fa construction uses the P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi add sum a5029caeb5fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L74-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L74-L89

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
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_add_sum_a5029caeb5fa {K : Type} {z : J → ℂ} (g : (J → ℂ) → ℝ) (f : K → (J → ℂ) → ℝ) (c : K → ℝ)
    (hg : ContDiffAt ℝ 2 g z) (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (w : J → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => g y + ∑ k ∈ s, c k * f k y) z ∧
      ReciprocityTheory.AnForm.levi (fun y => g y + ∑ k ∈ s, c k * f k y) z w =
        ReciprocityTheory.AnForm.levi g z w + ∑ k ∈ s, c k * ReciprocityTheory.AnForm.levi (f k) z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemipositiveTwist».«levi_add_sum» := P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_add_sum_a5029caeb5fa
