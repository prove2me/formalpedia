-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_abs_fsLogReg_le_7659ff6b41cf
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_abs_fsLogReg_le_7659ff6b41cf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:16.043531+00:00
-- url     : https://prove2.me/theorems/acb316f2-4f77-56f6-a3a8-18a67d18f55c
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact abs fs Log Reg le 7659ff6b41cf: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact abs fs Log Reg le 7659ff6b41cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact abs fs Log Reg le 7659ff6b41cf construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact abs fs Log Reg le 7659ff6b41cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L98-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L98-L116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit
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
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_abs_fsLogReg_le_7659ff6b41cf (h : HermNorm n) (u x : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : linEval u x ≠ 0) (hx : 0 < h.dualNorm x) :
    |fsLogReg h u ε x| ≤ 2 * |Real.log ‖linEval u x‖| + (2 * |Real.log (h.dualNorm x)| + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«abs_fsLogReg_le» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_abs_fsLogReg_le_7659ff6b41cf
