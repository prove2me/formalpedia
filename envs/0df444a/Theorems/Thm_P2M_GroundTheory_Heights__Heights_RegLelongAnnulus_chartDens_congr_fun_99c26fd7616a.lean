-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_congr_fun_99c26fd7616a
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_congr_fun_99c26fd7616a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:22.800901+00:00
-- url     : https://prove2.me/theorems/d2b65f85-0283-4dfc-a9be-1ca93d8efb49
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens congr fun 99c26fd7616a: P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens congr fun 99c26fd7616a
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens congr fun 99c26fd7616a construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus chart Dens congr fun 99c26fd7616a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L61-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L61-L79

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_congr_fun_99c26fd7616a {w : (Fin n → ℂ) → ℝ} {φ φ' : Fin m → (Fin n → ℂ) → ℝ}
    (hloc : ∀ z ∈ zeroSet J, w z ≠ 0 → ∀ k, φ k =ᶠ[𝓝 z] φ' k) (y : Fin m → ℂ) :
    chartDens J A w φ y = chartDens J A w φ' y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«chartDens_congr_fun» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_congr_fun_99c26fd7616a
