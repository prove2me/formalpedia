-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_upper_boundary_dct_real_axis_identification
-- name    : WeightedRootIntegralIdentity.upper_boundary_dct_real_axis_identification
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T10:21:20.41871+00:00
-- url     : https://prove2.me/theorems/25aad929-37a1-4a85-9cdf-7c71cfcfd4ca
-- title:
--   Upper-boundary DCT limit identified with the real-axis integrand
-- statement:
--   If dominated convergence gives convergence to the integral of a pointwise limit and that limit is pointwise equal to the real-axis integrand, then the upper-boundary integrals converge to the real-axis integral.
-- source:
--   Rewrite the DCT limit using the pointwise identification of the limiting integrand.

import Mathlib
open MeasureTheory Filter
open scoped Topology

namespace WeightedRootIntegralIdentity
open MeasureTheory Filter
open scoped Topology

theorem upper_boundary_dct_real_axis_identification {f : ℕ → ℝ → ℂ} {f₀ h : ℝ → ℂ} {μ : Measure ℝ}
    (hDCT : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, f₀ x ∂μ)))
    (hident : ∀ x, f₀ x = h x) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, h x ∂μ)) := by sorry

end WeightedRootIntegralIdentity
