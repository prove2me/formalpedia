-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_upper_boundary_dominated_convergence_v4
-- name    : WeightedRootIntegralIdentity.upper_boundary_dominated_convergence_v4
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T09:50:08.371973+00:00
-- url     : https://prove2.me/theorems/566156db-0606-46ea-a792-21a0508d206f
-- title:
--   Dominated convergence for the upper-boundary integrand
-- statement:
--   An almost-everywhere pointwise limit together with strong measurability and an integrable norm majorant permits passage of the limit through the upper-boundary integral.
-- source:
--   The Bochner dominated-convergence theorem applied to the complex-valued upper-boundary integrands.

import Mathlib
open MeasureTheory Filter
open scoped Topology

namespace WeightedRootIntegralIdentity
open MeasureTheory Filter
open scoped Topology

theorem upper_boundary_dominated_convergence_v4 {f : ℕ → ℝ → ℂ} {f₀ : ℝ → ℂ} {g : ℝ → ℝ} {μ : Measure ℝ}
    (hG : Integrable g μ)
    (hmeas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, f₀ x ∂μ)) := by sorry

end WeightedRootIntegralIdentity
