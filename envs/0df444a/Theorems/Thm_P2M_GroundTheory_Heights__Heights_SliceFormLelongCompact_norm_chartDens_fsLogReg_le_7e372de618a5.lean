-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_norm_chartDens_fsLogReg_le_7e372de618a5
-- name    : P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_norm_chartDens_fsLogReg_le_7e372de618a5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:44.95337+00:00
-- url     : https://prove2.me/theorems/d42df31d-f6c7-5499-bbc4-934bffe46de3
-- title:
--   P2 M Ground Theory Heights  Heights Slice Form Lelong Compact norm chart Dens fs Log Reg le 7e372de618a5: P2 M Ground Theory Heights  Heights Slice Form Lelong Compact norm chart Dens fs Log Reg le 7e
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Form Lelong Compact norm chart Dens fs Log Reg le 7e372de618a5 construction uses the P2 M Ground Theory Heights  Heights Slice Form Lelong Compact norm chart Dens fs Log Reg le 7e372de618a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L128-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceFormLelongCompactLimit.lean#L128-L158

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

theorem P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_norm_chartDens_fsLogReg_le_7e372de618a5 (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℝ} (φ : Fin d → (Fin n → ℂ) → ℝ) {R : ℝ}
    (hR : tsupport f ⊆ Metric.closedBall 0 R) (h0 : ∀ x ∈ zeroSet J, x ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {y : Fin (d + 1) → ℂ} (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    ‖chartDens J A (fsLogReg h u ε) (vecCons f φ) y‖ ≤
      2 * chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖)
          (vecCons f φ) y +
        chartAbsDens J A (fun x => 2 * |Real.log (h.dualNorm x)| + 1) (vecCons f φ) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceFormLelongCompact».«norm_chartDens_fsLogReg_le» := P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_norm_chartDens_fsLogReg_le_7e372de618a5
