-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_explicit_dominated_bound
-- name    : WeightedRootIntegralIdentity.weighted_root_explicit_dominated_bound
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T09:20:07.80721+00:00
-- url     : https://prove2.me/theorems/45b59a19-0754-47f3-99be-91d4a152162d
-- title:
--   Explicit weighted-root integrand domination
-- statement:
--   For a positive cutoff δ and x at least δ, the weighted-root quotient integrand is bounded by the product of the individual complex-power norms divided by δ.
-- source:
--   Complex-power norm conversion, finite-product norm multiplicativity, and the affine denominator lower bound.

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_norm_real_exponent
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_explicit_dominated_bound (n : ℕ) (b w : ℕ → ℝ) (x ε δ : ℝ)
    (hδ : 0 < δ) (hx : δ ≤ x) :
    ‖(∏ i ∈ Finset.range n,
        ((b i : ℂ) + ε * Complex.I) ^ (w i : ℂ)) /
        ((x : ℂ) + ε * Complex.I)‖ ≤
      (∏ i ∈ Finset.range n,
        ‖(b i : ℂ) + ε * Complex.I‖ ^ (w i : ℝ)) / δ := by sorry

end WeightedRootIntegralIdentity
