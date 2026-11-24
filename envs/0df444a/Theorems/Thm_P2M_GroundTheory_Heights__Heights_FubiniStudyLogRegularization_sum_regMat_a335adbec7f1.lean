-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sum_regMat_a335adbec7f1
-- name    : P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sum_regMat_a335adbec7f1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:56.368641+00:00
-- url     : https://prove2.me/theorems/bdbb67c9-3dc4-4e71-beff-bd43191afb44
-- title:
--   P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sum reg Mat a335adbec7f1: P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sum reg Mat a335adbec7f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sum reg Mat a335adbec7f1 construction uses the P2 M Ground Theory Heights  Heights Fubini Study Log Regularization sum reg Mat a335adbec7f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L95-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/FsLogRegBasic.lean#L95-L104

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

theorem P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sum_regMat_a335adbec7f1 (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 ≤ ε) (y : Fin n → ℂ) :
    ∑ i, ‖(regMat h u ε *ᵥ y) i‖ ^ 2 = ‖∑ j, u j * y j‖ ^ 2 + ε * sqDual h y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FubiniStudyLogRegularization».«sum_regMat» := P2M_GroundTheory_Heights__Heights_FubiniStudyLogRegularization_sum_regMat_a335adbec7f1
