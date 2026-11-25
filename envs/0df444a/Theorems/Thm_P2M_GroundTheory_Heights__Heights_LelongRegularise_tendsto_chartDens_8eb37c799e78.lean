-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_chartDens_8eb37c799e78
-- name    : P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_chartDens_8eb37c799e78
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:51.967387+00:00
-- url     : https://prove2.me/theorems/4344706a-2961-4afc-b46f-5c992650c8c7
-- title:
--   P2 M Ground Theory Heights  Heights Lelong Regularise tendsto chart Dens 8eb37c799e78: P2 M Ground Theory Heights  Heights Lelong Regularise tendsto chart Dens 8eb37c799e78
-- statement:
--   The P2 M Ground Theory Heights  Heights Lelong Regularise tendsto chart Dens 8eb37c799e78 construction uses the P2 M Ground Theory Heights  Heights Lelong Regularise tendsto chart Dens 8eb37c799e78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L181-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L181-L195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
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
open GroundTheory.Heights₂.Heights.LelongRegularise

theorem P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_chartDens_8eb37c799e78 {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    (ψ : Fin d → (Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    Tendsto (fun ε => chartDens J A (logReg u ε) ψ y) (𝓝[>] 0)
      (𝓝 (chartDens J A (fun x => Real.log ‖linEval u x‖) ψ y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LelongRegularise».«tendsto_chartDens» := P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_chartDens_8eb37c799e78
