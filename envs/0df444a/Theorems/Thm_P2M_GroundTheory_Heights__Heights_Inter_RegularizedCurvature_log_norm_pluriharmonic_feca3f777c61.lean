-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_norm_pluriharmonic_feca3f777c61
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_norm_pluriharmonic_feca3f777c61
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:34.506805+00:00
-- url     : https://prove2.me/theorems/5a6d9ea5-b1a9-42ce-9ae5-a043e5d72af4
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature log norm pluriharmonic feca3f777c61: P2 M Ground Theory Heights  Heights Inter Regularized Curvature log norm pluriharmonic feca3f777c61
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature log norm pluriharmonic feca3f777c61 construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature log norm pluriharmonic feca3f777c61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L107-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L107-L129

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_norm_pluriharmonic_feca3f777c61 {T : (J → ℂ) → ℂ} {z : J → ℂ} (hT : AnalyticAt ℂ T z) (h0 : T z ≠ 0)
    (w : J → ℂ) : ContDiffAt ℝ 2 (fun y => Real.log ‖T y‖) z ∧
      ReciprocityTheory.AnForm.levi (fun y => Real.log ‖T y‖) z w = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«log_norm_pluriharmonic» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_log_norm_pluriharmonic_feca3f777c61
