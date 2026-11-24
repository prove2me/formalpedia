-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_norm_chartDens_le_7e34c9bb0f45
-- name    : P2M_GroundTheory_Heights__Heights_LelongRegularise_norm_chartDens_le_7e34c9bb0f45
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:34.1062+00:00
-- url     : https://prove2.me/theorems/89f2fbdc-5e13-4eb8-8124-4618370af6ae
-- title:
--   P2 M Ground Theory Heights  Heights Lelong Regularise norm chart Dens le 7e34c9bb0f45: P2 M Ground Theory Heights  Heights Lelong Regularise norm chart Dens le 7e34c9bb0f45
-- statement:
--   The P2 M Ground Theory Heights  Heights Lelong Regularise norm chart Dens le 7e34c9bb0f45 construction uses the P2 M Ground Theory Heights  Heights Lelong Regularise norm chart Dens le 7e34c9bb0f45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L134-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L134-L179

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

theorem P2M_GroundTheory_Heights__Heights_LelongRegularise_norm_chartDens_le_7e34c9bb0f45 {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℝ} (φ : Fin d → (Fin n → ℂ) → ℝ) {R : ℝ}
    (hR : tsupport f ⊆ Metric.closedBall 0 R) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {y : Fin (d + 1) → ℂ}
    (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    ‖chartDens J A (logReg u ε) (vecCons f φ) y‖ ≤
      chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖)
          (vecCons f φ) y +
        chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval ((2 : ℂ) • u) x‖)
          (vecCons f φ) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LelongRegularise».«norm_chartDens_le» := P2M_GroundTheory_Heights__Heights_LelongRegularise_norm_chartDens_le_7e34c9bb0f45
