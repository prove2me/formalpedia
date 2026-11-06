-- Prove2me | Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
-- name    : RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:18.685698+00:00
-- url     : https://prove2.me/theorems/fc1c59b2-a617-4225-a88c-571a087e04c7
-- title:
--   L2 Compactness: norm smooth L2 sub extend By Zero L2 le of integral translate L2 sub extend By Zero L2 le
-- statement:
--   The L2 Compactness construction uses the norm smooth L2 sub extend By Zero L2 le of integral translate L2 sub extend By Zero L2 le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L67-L87
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L67-L87

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

theorem RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.norm_smoothL2_sub_extendByZeroL2_le_of_integral_translateL2_sub_extendByZeroL2_le
    (hK : IsCompact K) (hKm : MeasurableSet K)
    (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψint : ∫ x, ψ x ∂(volume : Measure E) = 1) {η : ℝ} (hη : 0 ≤ η)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K))
    (htrans :
      ∫ t,
          ‖(translateL2 (μ := (volume : Measure E)) (-t))
                (extendByZeroL2 (E := E) (K := K) hKm u)
              - extendByZeroL2 (E := E) (K := K) hKm u‖ ^ 2
        ∂kernelMeasure (E := E) ψ ≤ η ^ 2) :
    ‖smoothL2 (E := E) (K := K) ψ hK hKm hψc hψcs u
        - extendByZeroL2 (E := E) (K := K) hKm u‖ ≤ η := by sorry
