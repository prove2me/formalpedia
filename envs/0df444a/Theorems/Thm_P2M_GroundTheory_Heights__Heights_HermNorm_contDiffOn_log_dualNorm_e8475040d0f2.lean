-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_contDiffOn_log_dualNorm_e8475040d0f2
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_contDiffOn_log_dualNorm_e8475040d0f2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:49.068074+00:00
-- url     : https://prove2.me/theorems/e3852d85-4d23-5405-960c-7a97f9163989
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm cont Diff On log dual Norm e8475040d0f2: P2 M Ground Theory Heights  Heights Herm Norm cont Diff On log dual Norm e8475040d0f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm cont Diff On log dual Norm e8475040d0f2 construction uses the P2 M Ground Theory Heights  Heights Herm Norm cont Diff On log dual Norm e8475040d0f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutOffLimit.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutOffLimit.lean#L47-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
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
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_contDiffOn_log_dualNorm_e8475040d0f2 (h : HermNorm n) :
    ContDiffOn ℝ ∞ (fun y : Fin n → ℂ => Real.log (h.dualNorm y)) {y | y ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«contDiffOn_log_dualNorm» := P2M_GroundTheory_Heights__Heights_HermNorm_contDiffOn_log_dualNorm_e8475040d0f2
