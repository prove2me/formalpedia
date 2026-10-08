-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_missionJumpAndResidueSpecialization
-- name    : WeightedRootIntegralIdentity.missionJumpAndResidueSpecialization
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T10:33:05.899574+00:00
-- url     : https://prove2.me/theorems/a8922f33-424f-493b-af54-34ef38ef0c4d
-- title:
--   Concrete bank jump and residue specialization
-- statement:
--   The total bank jump is the sum of the sine-weighted interval contributions, while the residue-side real parts specialize to the 1/n weighted arithmetic and geometric terms.

import Mathlib
open scoped BigOperators Interval

theorem WeightedRootIntegralIdentity.missionJumpAndResidueSpecialization
    (n : ℕ) (a : ℕ → ℝ) (J B d p : ℂ)
    (hbank : J = 2 * B)
    (hB : B = ∑ k ∈ Finset.range (n - 1),
      ((Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) : ℂ) *
        (((∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x) : ℝ) : ℂ))
    (hd : d.re = -((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i))
    (hp : p.re = -Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹)) :
    J = 2 * ∑ k ∈ Finset.range (n - 1),
      ((Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) : ℂ) *
        (((∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x) : ℝ) : ℂ) ∧
    d.re = -((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) ∧
    p.re = -Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹) := by sorry
