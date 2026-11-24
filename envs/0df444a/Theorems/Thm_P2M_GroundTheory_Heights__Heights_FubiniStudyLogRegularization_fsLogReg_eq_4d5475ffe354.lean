-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_eq_4d5475ffe354
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_eq_4d5475ffe354
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:17.977396+00:00
-- url     : https://prove2.me/theorems/f6ea357f-c184-4953-ad1d-5578e672817a
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg eq 4d5475ffe354: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg eq 4d5475ffe354
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg eq 4d5475ffe354 construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg eq 4d5475ffe354 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L33-L35

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

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_eq_4d5475ffe354 (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) (y : Fin n → ℂ) :
    fsLogReg h u ε y = Real.log ((‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y) / sqDual h y) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«fsLogReg_eq» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_eq_4d5475ffe354
