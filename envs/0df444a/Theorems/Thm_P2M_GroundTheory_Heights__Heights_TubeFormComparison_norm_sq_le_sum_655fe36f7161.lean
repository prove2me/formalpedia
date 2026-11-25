-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_norm_sq_le_sum_655fe36f7161
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_norm_sq_le_sum_655fe36f7161
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:44.341642+00:00
-- url     : https://prove2.me/theorems/04acbf4b-eb55-4e0c-9f1b-4618bd85413b
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison norm sq le sum 655fe36f7161: P2 M Ground Theory Heights  Heights Tube Form Comparison norm sq le sum 655fe36f7161
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison norm sq le sum 655fe36f7161 construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison norm sq le sum 655fe36f7161 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L43-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeFormComparison

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_norm_sq_le_sum_655fe36f7161 {N : ℕ} (v : Fin N → ℂ) : ‖v‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«norm_sq_le_sum» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_norm_sq_le_sum_655fe36f7161
