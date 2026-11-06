-- Prove2me | Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_exists_kernel_tsupport_subset_ball_integral_eq_one
-- name    : RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.exists_kernel_tsupport_subset_ball_integral_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:52:56.056711+00:00
-- url     : https://prove2.me/theorems/ad03b32d-20fb-43fc-b91f-0d8771cbe57f
-- title:
--   L2 Compactness: exists kernel tsupport subset ball integral eq one
-- statement:
--   For any `deltaLoss > 0`, there exists a continuous compactly supported kernel `ψ` supported in
--   `Metric.ball 0 deltaLoss`, with `ψ ≥ 0` and `∫ ψ = 1` (w.r.t. Lebesgue measure).
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L52-L102
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/rellich-kondrachov-lean4341.patch#L52-L102

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
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
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceEL2CompactnessKernels
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceEL2CompactnessKernels
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceEL2CompactnessKernels

theorem RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.exists_kernel_tsupport_subset_ball_integral_eq_one {deltaLoss : ℝ} (hδ : 0 < deltaLoss) :
    ∃ ψ : E → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧
      (∫ x, ψ x ∂(volume : Measure E) = 1) ∧ tsupport ψ ⊆ Metric.ball (0 : E) deltaLoss := by sorry
