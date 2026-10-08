-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weightedRootProveJumpIdentity
-- name    : WeightedRootIntegralIdentity.weightedRootProveJumpIdentity
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T07:04:30.551525+00:00
-- url     : https://prove2.me/theorems/feb0040a-eeb7-48f4-b149-d3545ef86e88
-- title:
--   Concrete real-axis jump identity
-- statement:
--   If the upper-bank limit A is the purely imaginary integral of the real-axis imaginary part, then subtracting its conjugate gives twice i times that integral: A−conj(A)=2i∫ Im(F(x))/x dx.
-- source:
--   Use the accepted upper/lower boundary identification and conjugacy, followed by the elementary conjugation identity for a purely imaginary complex number.

import Mathlib
open scoped Interval
namespace WeightedRootIntegralIdentity
theorem weightedRootProveJumpIdentity
    (F : ℝ → ℂ) (a₀ a₁ : ℝ) (A : ℂ)
    (hA : A = Complex.I *
      (((∫ x in a₀..a₁, (F x).im / x) : ℝ) : ℂ)) :
    A - starRingEnd ℂ A =
      2 * Complex.I * (((∫ x in a₀..a₁, (F x).im / x) : ℝ) : ℂ) := by sorry
end WeightedRootIntegralIdentity
