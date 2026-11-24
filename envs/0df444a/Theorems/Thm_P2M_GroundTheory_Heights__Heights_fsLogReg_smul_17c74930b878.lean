-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fsLogReg_smul_17c74930b878
-- name    : P2M_GroundTheory_Heights__Heights_fsLogReg_smul_17c74930b878
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:15.409554+00:00
-- url     : https://prove2.me/theorems/7bf21349-57ec-471c-9dd9-6411459c85e9
-- title:
--   P2 M Ground Theory Heights  Heights fs Log Reg smul 17c74930b878: P2 M Ground Theory Heights  Heights fs Log Reg smul 17c74930b878
-- statement:
--   The P2 M Ground Theory Heights  Heights fs Log Reg smul 17c74930b878 construction uses the P2 M Ground Theory Heights  Heights fs Log Reg smul 17c74930b878 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutOffLimit.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutOffLimit.lean#L59-L67

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

theorem P2M_GroundTheory_Heights__Heights_fsLogReg_smul_17c74930b878 (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) (t : ℂ) (x : Fin n → ℂ)
    (ht : t ≠ 0) : fsLogReg h u ε (t • x) = fsLogReg h u ε x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fsLogReg_smul» := P2M_GroundTheory_Heights__Heights_fsLogReg_smul_17c74930b878
