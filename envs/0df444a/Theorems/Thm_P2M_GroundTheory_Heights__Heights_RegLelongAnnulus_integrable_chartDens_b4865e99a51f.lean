-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integrable_chartDens_b4865e99a51f
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integrable_chartDens_b4865e99a51f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:16:10.090851+00:00
-- url     : https://prove2.me/theorems/a40a0a74-ede9-4977-9a96-9da8ca8b9e2a
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus integrable chart Dens b4865e99a51f: P2 M Ground Theory Heights  Heights Reg Lelong Annulus integrable chart Dens b4865e99a51f
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus integrable chart Dens b4865e99a51f construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus integrable chart Dens b4865e99a51f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L105-L111

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integrable_chartDens_b4865e99a51f {φ : Fin m → (Fin n → ℂ) → ℝ} (hφ : ∀ k, SmoothNear (zeroSet J) (φ k))
    {f : (Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {C : ℝ} (hC : 0 ≤ C)
    {w : (Fin n → ℂ) → ℝ} (hwm : Measurable w) (hb : ∀ z, |w z| ≤ C * f z) :
    Integrable (chartDens J A w φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«integrable_chartDens» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integrable_chartDens_b4865e99a51f
