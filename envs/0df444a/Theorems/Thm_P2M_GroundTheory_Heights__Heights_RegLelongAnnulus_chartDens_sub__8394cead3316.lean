-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_sub__8394cead3316
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_sub__8394cead3316
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:07.99051+00:00
-- url     : https://prove2.me/theorems/56d8dc70-6fab-455c-86fd-5477ec1593ee
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens sub  8394cead3316: P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens sub  8394cead3316
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens sub  8394cead3316 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens sub  8394cead3316 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L81-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L81-L90

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_sub__8394cead3316 (hA : IsFiniteProjection J A) (c₁ c₂ : ℝ) (w₁ w₂ : (Fin n → ℂ) → ℝ)
    (φ : Fin m → (Fin n → ℂ) → ℝ) (y : Fin m → ℂ) :
    chartDens J A (fun z => c₁ * w₁ z - c₂ * w₂ z) φ y =
      c₁ * chartDens J A w₁ φ y - c₂ * chartDens J A w₂ φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«chartDens_sub'» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_sub__8394cead3316
