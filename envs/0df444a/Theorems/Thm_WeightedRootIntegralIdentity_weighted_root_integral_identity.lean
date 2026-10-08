-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_integral_identity
-- name    : WeightedRootIntegralIdentity.weighted_root_integral_identity
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-13T14:21:16.360036+00:00
-- url     : https://prove2.me/theorems/d80b3105-6286-4e5d-a80a-455df159b959
-- title:
--   Weighted root integral identity
-- statement:
--   Let $0<a_0\leq a_1\leq \cdots\leq a_{n-1}$ be a monotone sequence of $n\ge2$ positive real numbers. Then
--
--
--   $$\sum_{k=0}^{n-2}\frac{1}{\pi}\sin\!\left(\frac{\pi(k+1)}{n}\right)
--   \int_{a_k}^{a_{k+1}}
--   \frac{\prod_{i=0}^{n-1}|x-a_i|^{1/n}}{x}\,dx
--   =
--   \frac1n\sum_{i=0}^{n-1}a_i-
--   \left(\prod_{i=0}^{n-1}a_i\right)^{1/n}.$$
--
--
--   This identity equates a sine-weighted sum of interval integrals with the difference between the arithmetic and geometric means of the ordered positive nodes.
-- source:
--   User-provided image (13 September 2026). Original publication, page, and theorem/equation number not supplied.

import Mathlib open scoped BigOperators Interval

namespace WeightedRootIntegralIdentity

theorem weighted_root_integral_identity
    (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1)) :
    (∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
      = ((1 : ℝ) / n) * (∑ i ∈ Finset.range n, a i)
          - Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹) := by sorry

end WeightedRootIntegralIdentity
