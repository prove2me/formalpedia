-- Prove2me | Theorems.Thm_ValiantBorder_polynomialImageArc
-- name    : ValiantBorder.polynomialImageArc
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:29:08.670802+00:00
-- url     : https://prove2.me/theorems/d9235e24-f96c-4feb-8219-2608ceb6a936
-- title:
--   Laurent arcs for points in the closure of a polynomial image
-- statement:
--   Let $F$ be a polynomial map between finite-dimensional complex affine spaces. Suppose that at $p$ every polynomial relation that vanishes identically on the image vanishes as well. After a possible extension of the complex coefficient field, the input coordinates can be chosen as formal Laurent series so that each output is a power series with constant coefficient equal to the corresponding coordinate of $p$. This form of [Guo, Saxena and Sinhababu’s Theorem 15](https://doi.org/10.4230/LIPIcs.CCC.2018.10) suffices to compare coefficientwise limits of complex determinants with Laurent approximating circuits.
-- source:
--   Z. Guo, N. Saxena and A. Sinhababu, Algebraic Dependencies and PSPACE Algorithms in Approximative Complexity, CCC 2018, Theorem 15 and Lemmas 16–17, https://doi.org/10.4230/LIPIcs.CCC.2018.10. Translate the target to the origin and retain the Laurent-series conclusion. Their theorem allows coefficients in the algebraic closure of the base field, which is already ℂ here.

import Mathlib
open MvPolynomial

theorem ValiantBorder.polynomialImageArc :
  ∀ (I J : Type) [Fintype I] [Fintype J] (F : J → MvPolynomial I ℂ) (p : J → ℂ),
    (∀ g : MvPolynomial J ℂ, aeval F g = 0 → eval p g = 0) →
    ∃ (K : Type) (_ : Field K) (j : ℂ →+* K)
      (x : I → LaurentSeries K) (q : J → PowerSeries K),
      ∀ i, eval₂Hom ((algebraMap K (LaurentSeries K)).comp j) x (F i) = HahnSeries.ofPowerSeries ℤ K (q i) ∧
        PowerSeries.constantCoeff (q i) = j (p i) := by sorry
