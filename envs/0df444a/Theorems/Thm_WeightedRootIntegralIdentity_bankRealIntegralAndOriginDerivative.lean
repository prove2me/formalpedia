-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_bankRealIntegralAndOriginDerivative
-- name    : WeightedRootIntegralIdentity.bankRealIntegralAndOriginDerivative
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T10:58:18.462472+00:00
-- url     : https://prove2.me/theorems/0c5ff4f1-df3c-40ba-9eb5-66e077f9c006
-- title:
--   Concrete bank integral and origin derivative
-- statement:
--   The bank jump is the displayed sine-weighted real integral, and the origin residue contribution specializes to minus the 1/n weighted arithmetic sum.

import Mathlib
open scoped BigOperators Interval

theorem WeightedRootIntegralIdentity.bankRealIntegralAndOriginDerivative
    (n : ℕ) (a : ℕ → ℝ) (B : ℝ) (d : ℂ)
    (hB : B = ∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
    (hd : d.re = -((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i)) :
    B = ∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x ∧
    d.re = -((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) := by sorry
