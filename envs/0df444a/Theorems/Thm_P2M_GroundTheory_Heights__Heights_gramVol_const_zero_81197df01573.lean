-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gramVol_const_zero_81197df01573
-- name    : P2M_GroundTheory_Heights__Heights_gramVol_const_zero_81197df01573
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:48:06.45463+00:00
-- url     : https://prove2.me/theorems/65c0d60d-bf29-4105-8ee9-6f308c250a7b
-- title:
--   P2 M Ground Theory Heights  Heights gram Vol const zero 81197df01573: P2 M Ground Theory Heights  Heights gram Vol const zero 81197df01573
-- statement:
--   The P2 M Ground Theory Heights  Heights gram Vol const zero 81197df01573 construction uses the P2 M Ground Theory Heights  Heights gram Vol const zero 81197df01573 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeSheetGram.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeSheetGram.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGramLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeSheetGram
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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_gramVol_const_zero_81197df01573 {e n : ℕ} (y : Fin e → ℂ) :
    gramVol (fun _ : Fin e → ℂ => (0 : Fin n → ℂ)) y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gramVol_const_zero» := P2M_GroundTheory_Heights__Heights_gramVol_const_zero_81197df01573
