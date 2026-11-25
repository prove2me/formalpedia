-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_chartDens_42412aeabca1
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_chartDens_42412aeabca1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:04.512961+00:00
-- url     : https://prove2.me/theorems/f1912a60-5453-4987-bcb3-1bcb5265fcdf
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto chart Dens 42412aeabca1: P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto chart Dens 42412aeabca1
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto chart Dens 42412aeabca1 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus tendsto chart Dens 42412aeabca1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L50-L59

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_chartDens_42412aeabca1 (hA : IsFiniteProjection J A) {w : ℕ → (Fin n → ℂ) → ℝ} {w' : (Fin n → ℂ) → ℝ}
    (hw : ∀ z, Tendsto (fun k => w k z) atTop (𝓝 (w' z))) (φ : Fin m → (Fin n → ℂ) → ℝ) (y : Fin m → ℂ) :
    Tendsto (fun k => chartDens J A (w k) φ y) atTop (𝓝 (chartDens J A w' φ y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«tendsto_chartDens» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_chartDens_42412aeabca1
