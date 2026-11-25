-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_measurable_fsLogReg_f4332e7b3091
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_measurable_fsLogReg_f4332e7b3091
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:52.297203+00:00
-- url     : https://prove2.me/theorems/6e0376fe-c571-4847-9f4c-b41a55698d8b
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact measurable fs Log Reg f4332e7b3091: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact measurable fs Log Reg f4332e7b3091
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact measurable fs Log Reg f4332e7b3091 construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact measurable fs Log Reg f4332e7b3091 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L92-L96

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

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_measurable_fsLogReg_f4332e7b3091 (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) : Measurable (fsLogReg h u ε) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«measurable_fsLogReg» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_measurable_fsLogReg_f4332e7b3091
