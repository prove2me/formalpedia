-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_chartDens_le_fe914f30ce28
-- name    : P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_chartDens_le_fe914f30ce28
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:37.340801+00:00
-- url     : https://prove2.me/theorems/339e38a8-f650-4d1c-a857-2ca780c2c6a0
-- title:
--   P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs chart Dens le fe914f30ce28: P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs chart Dens le fe914f30ce28
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs chart Dens le fe914f30ce28 construction uses the P2 M Ground Theory Heights  Heights Reg Lelong Annulus abs chart Dens le fe914f30ce28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegLelongAnnulus.lean#L33-L48

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

theorem P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_chartDens_le_fe914f30ce28 (hA : IsFiniteProjection J A) {w f : (Fin n → ℂ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ z, |w z| ≤ C * f z) (φ : Fin m → (Fin n → ℂ) → ℝ) (y : Fin m → ℂ) :
    |chartDens J A w φ y| ≤ C * chartAbsDens J A f φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegLelongAnnulus».«abs_chartDens_le» := P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_chartDens_le_fe914f30ce28
