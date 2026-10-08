-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_missionFinalConstantNormalization
-- name    : WeightedRootIntegralIdentity.missionFinalConstantNormalization
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T11:02:20.558756+00:00
-- url     : https://prove2.me/theorems/a59350c3-2680-4e7f-8791-32a9d1fc5879
-- title:
--   Final constant normalization
-- statement:
--   The limiting contour balance, after collecting the factors of 2, pi, and i, is exactly the sine-weighted integral identity.

import Mathlib
open scoped BigOperators Interval

theorem WeightedRootIntegralIdentity.missionFinalConstantNormalization
    (n : ℕ) (a : ℕ → ℝ) (B : ℝ)
    (hB : B = ∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
    (hbalance : B = ((1 : ℝ) / n) * (∑ i ∈ Finset.range n, a i)
      - Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹)) :
    (∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
      = ((1 : ℝ) / n) * (∑ i ∈ Finset.range n, a i)
        - Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹) := by sorry
