-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_const_mul_2440ea3a0ba2
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_const_mul_2440ea3a0ba2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:07.834944+00:00
-- url     : https://prove2.me/theorems/ae86b2d3-19a9-4e21-90b4-b7d56d8df761
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens const mul 2440ea3a0ba2: P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens const mul 2440ea3a0ba2
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens const mul 2440ea3a0ba2 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens const mul 2440ea3a0ba2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L92-L99

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_const_mul_2440ea3a0ba2 (hA : IsFiniteProjection J A) (c : ℝ) (w : (Fin n → ℂ) → ℝ)
    (φ : Fin m → (Fin n → ℂ) → ℝ) (y : Fin m → ℂ) :
    chartDens J A (fun z => c * w z) φ y = c * chartDens J A w φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«chartDens_const_mul» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_const_mul_2440ea3a0ba2
