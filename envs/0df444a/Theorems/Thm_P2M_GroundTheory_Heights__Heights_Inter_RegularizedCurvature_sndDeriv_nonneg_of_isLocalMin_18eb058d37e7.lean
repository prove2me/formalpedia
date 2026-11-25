-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_sndDeriv_nonneg_of_isLocalMin_18eb058d37e7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_sndDeriv_nonneg_of_isLocalMin_18eb058d37e7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:21.255864+00:00
-- url     : https://prove2.me/theorems/b9af3eeb-c58f-45c5-a20a-de52e40d258e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularized Curvature snd Deriv nonneg of is Local Min 18eb058d37e7: P2 M Ground Theory Heights  Heights Inter Regularized Curvature snd Deriv nonneg of is Lo
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularized Curvature snd Deriv nonneg of is Local Min 18eb058d37e7 construction uses the P2 M Ground Theory Heights  Heights Inter Regularized Curvature snd Deriv nonneg of is Local Min 18eb058d37e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegularizedCurvature.lean#L59-L67

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_sndDeriv_nonneg_of_isLocalMin_18eb058d37e7 {f : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hmin : IsLocalMin f z) (e : J → ℂ) : 0 ≤ fderiv ℝ (fderiv ℝ f) z e e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularizedCurvature».«sndDeriv_nonneg_of_isLocalMin» := P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_sndDeriv_nonneg_of_isLocalMin_18eb058d37e7
