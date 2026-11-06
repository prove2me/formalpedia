-- Prove2me | Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
-- name    : RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:07.683805+00:00
-- url     : https://prove2.me/theorems/663b7e57-9988-4691-847a-06ebef1cd4d2
-- title:
--   L2 Compactness: integral norm sq translate L2 sub le sq of tsupport subset ball
-- statement:
--   The L2 Compactness construction uses the integral norm sq translate L2 sub le sq of tsupport subset ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L77-L135
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L77-L135

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceEL2CompactnessTranslationIntegral
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceEL2CompactnessTranslationIntegral
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceEL2CompactnessTranslationIntegral
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableAddEL2CompactnessTranslationIntegral
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableNegEL2CompactnessTranslationIntegral
attribute [local instance] instMeasurableSpaceEL2CompactnessTranslationIntegral instBorelSpaceEL2CompactnessTranslationIntegral instOpensMeasurableSpaceEL2CompactnessTranslationIntegral instMeasurableAddEL2CompactnessTranslationIntegral instMeasurableNegEL2CompactnessTranslationIntegral
variable {ψ : E → ℝ}

theorem RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.integral_norm_sq_translateL2_sub_le_sq_of_tsupport_subset_ball
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1)
    {deltaLoss η : ℝ} (hη : 0 ≤ η) (hψsupp : tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss)
    (F : (E →₂[(volume : Measure E)] ℝ))
    (hmod :
      ∀ t : E, t ∈ Metric.ball (0 : E) deltaLoss →
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ≤ η) :
    ∫ t,
        ‖(translateL2 (μ := (volume : Measure E)) (-t)) F - F‖ ^ 2
      ∂kernelMeasure (E := E) ψ ≤ η ^ 2 := by sorry
