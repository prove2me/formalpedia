-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_zero_fun_1d97ee7a5fc5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_zero_fun_1d97ee7a5fc5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:20.860434+00:00
-- url     : https://prove2.me/theorems/7e3cf31a-2266-5dfe-abf2-cf3a5b90d696
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi zero fun 1d97ee7a5fc5: P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi zero fun 1d97ee7a5fc5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi zero fun 1d97ee7a5fc5 construction uses the P2 M Ground Theory Heights  Heights Inter Semipositive Twist levi zero fun 1d97ee7a5fc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L91-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemiPosTwist.lean#L91-L92

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_zero_fun_1d97ee7a5fc5 (z w : J → ℂ) : ReciprocityTheory.AnForm.levi (fun _ : J → ℂ => (0 : ℝ)) z w = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemipositiveTwist».«levi_zero_fun» := P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_zero_fun_1d97ee7a5fc5
