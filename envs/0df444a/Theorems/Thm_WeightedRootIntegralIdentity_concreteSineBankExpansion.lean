-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_concreteSineBankExpansion
-- name    : WeightedRootIntegralIdentity.concreteSineBankExpansion
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T10:25:04.382816+00:00
-- url     : https://prove2.me/theorems/5ae9cad6-c50d-44aa-a8f7-1b50c3c84a9f
-- title:
--   Concrete sine-weighted bank expansion
-- statement:
--   The concrete bank expression uses the mission weights sin(pi(k+1)/n)/pi on each ordered interval, exactly matching the displayed sine-weighted sum.

import Mathlib
open scoped BigOperators Interval

theorem WeightedRootIntegralIdentity.concreteSineBankExpansion
    (n : ℕ) (a : ℕ → ℝ)
    (B : ℝ)
    (hB : B = ∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x) :
    B = ∑ k ∈ Finset.range (n - 1),
      ((Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) : ℝ) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x := by sorry
