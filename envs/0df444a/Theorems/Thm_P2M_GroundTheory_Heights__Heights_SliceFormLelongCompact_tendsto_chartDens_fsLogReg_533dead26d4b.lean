-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_chartDens_fsLogReg_533dead26d4b
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_chartDens_fsLogReg_533dead26d4b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:25.31389+00:00
-- url     : https://prove2.me/theorems/72bdffb3-fa62-47fd-8cd0-a1160e628030
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto chart Dens fs Log Reg 533dead26d4b: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto chart Dens fs Log Reg 53
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto chart Dens fs Log Reg 533dead26d4b construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact tendsto chart Dens fs Log Reg 533dead26d4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L160-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L160-L176

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

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_chartDens_fsLogReg_533dead26d4b (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : IsFiniteProjection J A) (u : Fin n → ℂ)
    (ψ : Fin d → (Fin n → ℂ) → ℝ) (h0 : ∀ x ∈ zeroSet J, x ≠ 0) {y : Fin d → ℂ}
    (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    Tendsto (fun ε => chartDens J A (fsLogReg h u ε) ψ y) (𝓝[>] 0)
      (𝓝 (chartDens J A (fun x => Real.log ‖linEval u x‖) ψ y -
        chartDens J A (fun x => Real.log (h.dualNorm x)) ψ y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«tendsto_chartDens_fsLogReg» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_chartDens_fsLogReg_533dead26d4b
