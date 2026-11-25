-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_integral_chartDens_4b0362defe49
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_integral_chartDens_4b0362defe49
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:44.58263+00:00
-- url     : https://prove2.me/theorems/9e514aaa-cbbc-5da2-9836-aec9ace3fa8c
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto integral chart Dens 4b0362defe49: P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto integral chart Dens 4b0362defe49
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto integral chart Dens 4b0362defe49 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto integral chart Dens 4b0362defe49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L113-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L113-L123

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
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
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
variable {n m : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin m) (Fin n) ℂ}
variable (hCM : ChartMassCompact.Statement) (hJ : J.IsPrime)
  (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (m : ℕ)) (hA : IsFiniteProjection J A)
include hCM hJ hdim hA

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_integral_chartDens_4b0362defe49 {φ : Fin m → (Fin n → ℂ) → ℝ} (hφ : ∀ k, SmoothNear (zeroSet J) (φ k))
    {f : (Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {C : ℝ} (hC : 0 ≤ C)
    {w : ℕ → (Fin n → ℂ) → ℝ} {w' : (Fin n → ℂ) → ℝ} (hwm : ∀ k, Measurable (w k))
    (hb : ∀ k z, |w k z| ≤ C * f z) (hw : ∀ z, Tendsto (fun k => w k z) atTop (𝓝 (w' z))) :
    Tendsto (fun k => ∫ y, chartDens J A (w k) φ y) atTop (𝓝 (∫ y, chartDens J A w' φ y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«tendsto_integral_chartDens» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_integral_chartDens_4b0362defe49
