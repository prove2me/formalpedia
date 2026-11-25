-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_logReg_37400dfe8e65
-- name    : P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_logReg_37400dfe8e65
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:58.712862+00:00
-- url     : https://prove2.me/theorems/7c1fed9b-bacb-4fef-a8d4-52adfaeca801
-- title:
--   P2 M Ground Theory Heights  Heights Lelong Regularise tendsto log Reg 37400dfe8e65: P2 M Ground Theory Heights  Heights Lelong Regularise tendsto log Reg 37400dfe8e65
-- statement:
--   The P2 M Ground Theory Heights  Heights Lelong Regularise tendsto log Reg 37400dfe8e65 construction uses the P2 M Ground Theory Heights  Heights Lelong Regularise tendsto log Reg 37400dfe8e65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L79-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L79-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
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
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LelongRegularise

theorem P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_logReg_37400dfe8e65 {n : ℕ} (u x : Fin n → ℂ) (hx : linEval u x ≠ 0) :
    Tendsto (fun ε => logReg u ε x) (𝓝[>] 0) (𝓝 (Real.log ‖linEval u x‖)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LelongRegularise».«tendsto_logReg» := P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_logReg_37400dfe8e65
