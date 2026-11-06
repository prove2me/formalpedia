-- Prove2me | Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
-- name    : RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:03.545875+00:00
-- url     : https://prove2.me/theorems/88a55d4d-a317-41ea-87e8-77bbe09306c1
-- title:
--   L2 Compactness: totally Bounded extend By Zero L2 image of forall exists translation Integral small
-- statement:
--   The L2 Compactness construction uses the totally Bounded extend By Zero L2 image of forall exists translation Integral small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L89-L161
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L89-L161

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Approximation
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Transfer
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceEL2CompactnessFrechetKolmogorov
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceEL2CompactnessFrechetKolmogorov
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceEL2CompactnessFrechetKolmogorov
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableAddEL2CompactnessFrechetKolmogorov
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableNegEL2CompactnessFrechetKolmogorov
variable {K : Set E} {ψ : E → ℝ}

theorem RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.totallyBounded_extendByZeroL2_image_of_forall_exists_translationIntegral_small
    (hK : IsCompact K) (hKm : MeasurableSet K) {R : ℝ} (hR : 0 ≤ R)
    {A : Set (MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))}
    (hA : A ⊆ Metric.closedBall (0 : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) R)
    (hApprox :
      ∀ ε : ℝ, 0 < ε →
        ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
          (∫ x, ψ x ∂(volume : Measure E) = 1) ∧
          ∀ u ∈ A,
            ∫ t,
                ‖(translateL2 (μ := (volume : Measure E)) (-t))
                      (extendByZeroL2 (E := E) (K := K) hKm u)
                    - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
              ∂kernelMeasure (E := E) ψ ≤ (ε / 2) ^ 2) :
    TotallyBounded (extendByZeroL2 (E := E) (K := K) hKm '' A) := by sorry
