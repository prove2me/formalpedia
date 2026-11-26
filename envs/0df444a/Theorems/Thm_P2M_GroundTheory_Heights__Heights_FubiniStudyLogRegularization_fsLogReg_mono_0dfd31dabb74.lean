-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_mono_0dfd31dabb74
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_mono_0dfd31dabb74
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:14:59.067985+00:00
-- url     : https://prove2.me/theorems/18c214aa-168d-59c0-8c3d-0fa872554e8f
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg mono 0dfd31dabb74: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg mono 0dfd31dabb74
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg mono 0dfd31dabb74 construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization fs Log Reg mono 0dfd31dabb74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L72-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L72-L83

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

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_mono_0dfd31dabb74 (h : HermNorm n) (u : Fin n → ℂ) {δ δ' : ℝ} (hδ : 0 < δ) (hδδ' : δ ≤ δ')
    (y : Fin n → ℂ) : fsLogReg h u δ y ≤ fsLogReg h u δ' y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«fsLogReg_mono» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_fsLogReg_mono_0dfd31dabb74
