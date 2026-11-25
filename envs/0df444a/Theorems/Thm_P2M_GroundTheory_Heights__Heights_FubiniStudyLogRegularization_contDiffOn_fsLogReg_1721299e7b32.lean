-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiffOn_fsLogReg_1721299e7b32
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiffOn_fsLogReg_1721299e7b32
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:14:13.796837+00:00
-- url     : https://prove2.me/theorems/7de4e898-dd4a-503b-9cd6-5d5d6053373e
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff On fs Log Reg 1721299e7b32: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff On fs Log Reg 17
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff On fs Log Reg 1721299e7b32 construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff On fs Log Reg 1721299e7b32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L46-L59

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

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiffOn_fsLogReg_1721299e7b32 (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fsLogReg h u ε) {x | x ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«contDiffOn_fsLogReg» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiffOn_fsLogReg_1721299e7b32
