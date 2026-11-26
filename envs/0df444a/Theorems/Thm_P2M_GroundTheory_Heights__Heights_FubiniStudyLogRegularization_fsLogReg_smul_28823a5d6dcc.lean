-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_smul_28823a5d6dcc
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_smul_28823a5d6dcc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:14:51.76703+00:00
-- url     : https://prove2.me/theorems/a099d7d4-e43d-57f4-af6d-58dd50a54e46
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg smul 28823a5d6dcc: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg smul 28823a5d6dcc
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg smul 28823a5d6dcc construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg smul 28823a5d6dcc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L61-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L61-L70

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

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_smul_28823a5d6dcc (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) {t : ℂ} (ht : t ≠ 0)
    (y : Fin n → ℂ) : fsLogReg h u ε (t • y) = fsLogReg h u ε y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«fsLogReg_smul» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_smul_28823a5d6dcc
