-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_measurable_fsLogReg_19b65a2a6887
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_measurable_fsLogReg_19b65a2a6887
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:14:33.797146+00:00
-- url     : https://prove2.me/theorems/80c74d72-35ee-5f64-b32a-d2eab2e3adc2
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization measurable fs Log Reg 19b65a2a6887: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization measurable fs Log Reg 19b65a
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization measurable fs Log Reg 19b65a2a6887 construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization measurable fs Log Reg 19b65a2a6887 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L85-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L85-L93

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

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_measurable_fsLogReg_19b65a2a6887 (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) :
    Measurable (fsLogReg h u ε) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«measurable_fsLogReg» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_measurable_fsLogReg_19b65a2a6887
