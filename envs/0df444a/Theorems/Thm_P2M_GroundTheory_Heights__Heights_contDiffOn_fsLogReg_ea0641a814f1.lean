-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiffOn_fsLogReg_ea0641a814f1
-- name    : P2M_GroundTheory_Heights__Heights_contDiffOn_fsLogReg_ea0641a814f1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:06.463803+00:00
-- url     : https://prove2.me/theorems/5859bd8c-e533-444e-a2fe-dbada3a5715e
-- title:
--   P2 M Ground Theory Heights  Heights cont Diff On fs Log Reg ea0641a814f1: P2 M Ground Theory Heights  Heights cont Diff On fs Log Reg ea0641a814f1
-- statement:
--   The P2 M Ground Theory Heights  Heights cont Diff On fs Log Reg ea0641a814f1 construction uses the P2 M Ground Theory Heights  Heights cont Diff On fs Log Reg ea0641a814f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutOffLimit.lean#L69-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutOffLimit.lean#L69-L79

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

theorem P2M_GroundTheory_Heights__Heights_contDiffOn_fsLogReg_ea0641a814f1 (h : HermNorm n) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fsLogReg h u ε) {y | y ≠ 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«contDiffOn_fsLogReg» := P2M_GroundTheory_Heights__Heights_contDiffOn_fsLogReg_ea0641a814f1
