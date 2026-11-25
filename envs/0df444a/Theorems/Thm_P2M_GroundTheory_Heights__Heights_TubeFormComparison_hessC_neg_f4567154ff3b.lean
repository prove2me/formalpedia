-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_neg_f4567154ff3b
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_neg_f4567154ff3b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:42:04.074013+00:00
-- url     : https://prove2.me/theorems/28a9847b-f23a-401a-a718-905738511cc0
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison hess C neg f4567154ff3b: P2 M Ground Theory Heights  Heights Tube Form Comparison hess C neg f4567154ff3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison hess C neg f4567154ff3b construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison hess C neg f4567154ff3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L60-L64

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

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_neg_f4567154ff3b {N : ℕ} (φ : (Fin N → ℂ) → ℝ) (z : Fin N → ℂ) :
    hessC (fun y => -φ y) z = -hessC φ z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«hessC_neg» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_neg_f4567154ff3b
