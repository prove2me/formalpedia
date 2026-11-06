-- Prove2me | Theorems.Thm_P2M_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_extendByZeroL2_eq_extendByZero___cc8208de3560
-- name    : P2M_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_extendByZeroL2_eq_extendByZero___cc8208de3560
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:05.069501+00:00
-- url     : https://prove2.me/theorems/c186ce03-cb75-4d99-a6df-da4ff82ef43f
-- title:
--   P2 M Rellich Kondrachov Analysis Functional Spaces Sobolev Euclidean L2 Compactness extend By Zero L2 eq extend By Zero   cc8208de3560: P2 M Rellich Kondrachov Analysis Functional Spaces Sobolev Eucli
-- statement:
--   The P2 M Rellich Kondrachov Analysis Functional Spaces Sobolev Euclidean L2 Compactness extend By Zero L2 eq extend By Zero   cc8208de3560 construction uses the P2 M Rellich Kondrachov Analysis Functional Spaces Sobolev Euclidean L2 Compactness extend By Zero L2 eq extend By Zero   cc8208de3560 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L115-L134
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L115-L134

import Definitions.Def_RellichKondrachov_MeasureTheory_Function_LpSpace_Restrict
import Mathlib.Analysis.Convolution
import Mathlib.Topology.Algebra.Support
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
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
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceSmoothing1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceSmoothing1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceSmoothing1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableAddSmoothing1
variable {K : Set E}

theorem P2M_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_extendByZeroL2_eq_extendByZero___cc8208de3560 (hKm : MeasurableSet K)
    (u : MeasureTheory.Lp ℝ (2 : ℝ≥0∞) (volume.restrict K)) :
    extendByZeroL2 (E := E) (K := K) hKm u =
      (MeasureTheory.Lp.extendByZeroₗᵢ (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞))
        (s := K) hKm) u := by sorry

alias «RellichKondrachov».«Analysis».«FunctionalSpaces».«Sobolev».«Euclidean».«L2Compactness».«extendByZeroL2_eq_extendByZeroₗᵢ» := P2M_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_extendByZeroL2_eq_extendByZero___cc8208de3560
