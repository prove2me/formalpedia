-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_add_log_0720d50c2495
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_add_log_0720d50c2495
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:24:55.532698+00:00
-- url     : https://prove2.me/theorems/394c5f18-42df-4f49-958c-35e78c2a624a
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg add log 0720d50c2495: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg add log 0720d50c2495
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg add log 0720d50c2495 construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg add log 0720d50c2495 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L122-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L122-L132

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FsLogRegBasic
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
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.FubiniStudyLogRegularization
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_add_log_0720d50c2495 (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) (y : Fin n → ℂ) :
    fsLogReg h u ε y + Real.log (h.dualNorm y) = Real.log √(∑ i, ‖(regMat h u ε *ᵥ y) i‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«fsLogReg_add_log» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_add_log_0720d50c2495
