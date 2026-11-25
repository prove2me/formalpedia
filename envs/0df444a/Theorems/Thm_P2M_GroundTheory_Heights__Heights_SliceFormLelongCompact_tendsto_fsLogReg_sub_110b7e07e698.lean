-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_fsLogReg_sub_110b7e07e698
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_fsLogReg_sub_110b7e07e698
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:20.150204+00:00
-- url     : https://prove2.me/theorems/8f02619e-7fa7-55cd-bbd5-8c3caac95e9a
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto fs Log Reg sub 110b7e07e698: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto fs Log Reg sub 110b7e07e698
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto fs Log Reg sub 110b7e07e698 construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto fs Log Reg sub 110b7e07e698 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L118-L126

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

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_fsLogReg_sub_110b7e07e698 (h : HermNorm n) (u x : Fin n → ℂ) (hu : linEval u x ≠ 0)
    (hx : 0 < h.dualNorm x) :
    Tendsto (fun ε => fsLogReg h u ε x) (𝓝[>] 0)
      (𝓝 (Real.log ‖linEval u x‖ - Real.log (h.dualNorm x))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«tendsto_fsLogReg_sub» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_fsLogReg_sub_110b7e07e698
