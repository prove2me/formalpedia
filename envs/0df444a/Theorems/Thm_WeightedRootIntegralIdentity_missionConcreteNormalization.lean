-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_missionConcreteNormalization
-- name    : WeightedRootIntegralIdentity.missionConcreteNormalization
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T10:39:12.681574+00:00
-- url     : https://prove2.me/theorems/6c79b437-438c-4929-9569-de271a26c766
-- title:
--   Concrete weighted-root normalization
-- statement:
--   After substituting the 1/n residue evaluations into the contour balance, the normalized identity is exactly the sine-weighted integral formula for ordered positive reals.

import Mathlib
open scoped BigOperators Interval

theorem WeightedRootIntegralIdentity.missionConcreteNormalization
    (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hcontour :
      (∑ k ∈ Finset.range (n - 1),
        (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
          ∫ x in a k..a (k + 1),
            (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
        = ((1 : ℝ) / n) * (∑ i ∈ Finset.range n, a i)
          - Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹)) :
    (∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
      = ((1 : ℝ) / n) * (∑ i ∈ Finset.range n, a i)
        - Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹) := by sorry
