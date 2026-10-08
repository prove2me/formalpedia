-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_cpow_ordered_interval_boundary
-- name    : WeightedRootIntegralIdentity.cpow_ordered_interval_boundary
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-13T15:14:23.685888+00:00
-- url     : https://prove2.me/theorems/bb40d4fb-b392-4f4a-a69b-24c8ae77885a
-- title:
--   Boundary phase between consecutive ordered nodes
-- statement:
--   Let $a_0\le\cdots\le a_{n-1}$, choose $k<n-1$, and suppose $a_k<x<a_{k+1}$. Then
--
--   $$
--   \prod_{i=0}^{n-1}(a_i-x)^{w_i}
--   =
--   \left(\prod_{i=0}^{n-1}|a_i-x|^{w_i}\right)
--   \exp\left(i\pi\sum_{i=0}^k w_i\right).
--   $$
--
--   Exactly the factors indexed by $i\le k$ are negative. This identifies the cumulative phase on one interval between consecutive ordered nodes and is the pointwise boundary value needed for the sine-weighted jump formula.
-- source:
--   Interval specialization of the boundary phase calculation in https://math.stackexchange.com/questions/4244874/can-we-prove-am-gm-inequality-using-these-integrals, first answer, where N(x) is constant between consecutive ordered nodes.

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_finset_boundary_product
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem cpow_ordered_interval_boundary
    (n k : ℕ) (a w : ℕ → ℝ)
    (hk : k < n - 1)
    (hmono : ∀ i j, i < j → j < n → a i ≤ a j)
    (x : ℝ) (hxlo : a k < x) (hxhi : x < a (k + 1)) :
    (∏ i ∈ Finset.range n, (((a i - x : ℝ) : ℂ) ^ (w i : ℂ))) =
      ((∏ i ∈ Finset.range n, Real.rpow |a i - x| (w i) : ℝ) : ℂ) *
        Complex.exp
          ((((Real.pi * (∑ i ∈ Finset.range (k + 1), w i) : ℝ) : ℝ) : ℂ) *
            Complex.I) := by sorry

end WeightedRootIntegralIdentity
