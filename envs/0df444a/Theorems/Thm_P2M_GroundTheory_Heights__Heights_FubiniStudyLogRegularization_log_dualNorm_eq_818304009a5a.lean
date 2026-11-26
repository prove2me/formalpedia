-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_log_dualNorm_eq_818304009a5a
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_log_dualNorm_eq_818304009a5a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:24:52.149433+00:00
-- url     : https://prove2.me/theorems/08c67b76-8e36-4597-806f-b7429de8f7eb
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization log dual Norm eq 818304009a5a: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization log dual Norm eq 818304009a5a
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization log dual Norm eq 818304009a5a construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization log dual Norm eq 818304009a5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L117-L120

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

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_log_dualNorm_eq_818304009a5a (h : HermNorm n) (y : Fin n → ℂ) :
    Real.log (h.dualNorm y) = Real.log √(∑ i, ‖(regMat h 0 1 *ᵥ y) i‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«log_dualNorm_eq» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_log_dualNorm_eq_818304009a5a
