-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logReg_zero_ca923fd2cacc
-- name    : P2M_GroundTheory_Heights__Heights_logReg_zero_ca923fd2cacc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:49:42.165051+00:00
-- url     : https://prove2.me/theorems/814c4eac-3813-5392-8535-87ba3420cc1a
-- title:
--   P2 M Ground Theory Heights  Heights log Reg zero ca923fd2cacc: P2 M Ground Theory Heights  Heights log Reg zero ca923fd2cacc
-- statement:
--   The P2 M Ground Theory Heights  Heights log Reg zero ca923fd2cacc construction uses the P2 M Ground Theory Heights  Heights log Reg zero ca923fd2cacc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLelongRegularise.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLelongRegularise.lean#L29-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
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

theorem P2M_GroundTheory_Heights__Heights_logReg_zero_ca923fd2cacc (u : Fin n → ℂ) (x : Fin n → ℂ) :
    logReg u 0 x = Real.log ‖linEval u x‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logReg_zero» := P2M_GroundTheory_Heights__Heights_logReg_zero_ca923fd2cacc
