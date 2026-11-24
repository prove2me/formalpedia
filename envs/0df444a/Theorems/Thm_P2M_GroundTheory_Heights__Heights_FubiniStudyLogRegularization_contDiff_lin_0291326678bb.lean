-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_lin_0291326678bb
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_lin_0291326678bb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:47.991749+00:00
-- url     : https://prove2.me/theorems/780bd28b-e20b-4f44-bba4-2bba3ba268af
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff lin 0291326678bb: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff lin 0291326678bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff lin 0291326678bb construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization cont Diff lin 0291326678bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L43-L44

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

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_lin_0291326678bb (u : Fin n → ℂ) : ContDiff ℝ ∞ fun y : Fin n → ℂ => ‖∑ j, u j * y j‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«contDiff_lin» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_contDiff_lin_0291326678bb
