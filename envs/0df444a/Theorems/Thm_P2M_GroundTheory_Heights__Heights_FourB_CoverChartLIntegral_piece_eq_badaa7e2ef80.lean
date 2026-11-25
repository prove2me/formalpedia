-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_piece_eq_badaa7e2ef80
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_piece_eq_badaa7e2ef80
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:27.874692+00:00
-- url     : https://prove2.me/theorems/76d105ef-86d0-5c7c-86f9-b2d212739d15
-- title:
--   P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral piece eq badaa7e2ef80: P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral piece eq badaa7e2ef80
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral piece eq badaa7e2ef80 construction uses the P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral piece eq badaa7e2ef80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L162-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L162-L225

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PCoverChartLIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm.M MeasureTheory Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_piece_eq_badaa7e2ef80 {A : FinHolAtlas e X} (χ : ChartPartition A) (j : Fin A.n) {q : X → Fin e → ℂ}
    {M₀ : Set X} (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {W : Set X} (hWo : IsOpen W)
    (hWM : W ⊆ M₀) {U B : Set (Fin e → ℂ)} (hUo : IsOpen U) (hB : MeasurableSet B)
    (hBU : B ⊆ U) {s : (Fin e → ℂ) → X} (hsc : ContinuousOn s U)
    (hsU : ∀ u ∈ U, s u ∈ W ∧ q (s u) = u) (hsW : ∀ x ∈ W, q x ∈ U ∧ s (q x) = x)
    (g : (Fin e → ℂ) → ENNReal) :
    ∫⁻ y in ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) ∩ (q ∘ (A.chart j).symm) ⁻¹' B,
        ENNReal.ofReal (χ.χ j ((A.chart j).symm y)) *
          ENNReal.ofReal (‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
            (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2) * g (q ((A.chart j).symm y)) =
      ∫⁻ u in B, ENNReal.ofReal (χ.χ j (s u)) * g u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CoverChartLIntegral».«piece_eq» := P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_piece_eq_badaa7e2ef80
