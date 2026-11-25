-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_neg_eba6193b69bd
-- name    : P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_neg_eba6193b69bd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:56.94293+00:00
-- url     : https://prove2.me/theorems/0b24fcb8-b198-4222-acb7-40ef175f14ca
-- title:
--   P2 M Ground Theory Heights  Heights Tube Form Comparison levi neg eba6193b69bd: P2 M Ground Theory Heights  Heights Tube Form Comparison levi neg eba6193b69bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Form Comparison levi neg eba6193b69bd construction uses the P2 M Ground Theory Heights  Heights Tube Form Comparison levi neg eba6193b69bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeFormCompare.lean#L52-L58

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

theorem P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_neg_eba6193b69bd {N : ℕ} (φ : (Fin N → ℂ) → ℝ) (z w : Fin N → ℂ) :
    levi (fun y => -φ y) z w = -levi φ z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeFormComparison».«levi_neg» := P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_neg_eba6193b69bd
