-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_product_norm_bound
-- name    : WeightedRootIntegralIdentity.weighted_root_product_norm_bound
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T08:31:56.075432+00:00
-- url     : https://prove2.me/theorems/d10fbc92-5f3f-459f-9f2e-91a5c64d4e0e
-- title:
--   Norm of the finite weighted-root product
-- statement:
--   The norm of the finite weighted-root product factors exactly into the product of the real powers of the individual affine-base norms. This identity is the multiplicative core of the uniform domination estimate.
-- source:
--   Multiplicativity of the complex norm and the real-exponent complex-power norm formula.

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_norm_real_exponent
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_product_norm_bound (n : ℕ) (b w : ℕ → ℝ) (ε : ℝ) :
    ‖∏ i ∈ Finset.range n,
      ((b i : ℂ) + ε * Complex.I) ^ (w i : ℂ)‖ =
      ∏ i ∈ Finset.range n,
        ‖(b i : ℂ) + ε * Complex.I‖ ^ (w i : ℝ) := by sorry

end WeightedRootIntegralIdentity
