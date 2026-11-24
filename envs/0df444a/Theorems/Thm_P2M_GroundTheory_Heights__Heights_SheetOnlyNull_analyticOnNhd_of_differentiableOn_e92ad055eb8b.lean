-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_of_differentiableOn_e92ad055eb8b
-- name    : P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_of_differentiableOn_e92ad055eb8b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:17.331006+00:00
-- url     : https://prove2.me/theorems/987d3d92-2a1b-4726-a482-a81ab4763b43
-- title:
--   P2 M Ground Theory Heights  Heights Sheet Only Null analytic On Nhd of differentiable On e92ad055eb8b: P2 M Ground Theory Heights  Heights Sheet Only Null analytic On Nhd of differentiable On e92ad055
-- statement:
--   The P2 M Ground Theory Heights  Heights Sheet Only Null analytic On Nhd of differentiable On e92ad055eb8b construction uses the P2 M Ground Theory Heights  Heights Sheet Only Null analytic On Nhd of differentiable On e92ad055eb8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetOnlyNull.lean#L35-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.SheetOnlyNull
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_of_differentiableOn_e92ad055eb8b {m : ℕ} {U : Set (Fin d → ℂ)}
    {F : (Fin d → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    AnalyticOnNhd ℂ F U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SheetOnlyNull».«analyticOnNhd_of_differentiableOn» := P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_of_differentiableOn_e92ad055eb8b
