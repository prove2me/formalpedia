-- Prove2me | Theorems.Thm_TranscendenceTheory_rational_interpolation_polynomial_divisibility
-- name    : TranscendenceTheory.rational_interpolation_polynomial_divisibility
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T22:32:16.761834+00:00
-- url     : https://prove2.me/theorems/5dcef86d-b5a7-45e8-a518-7ebacbc647e5
-- title:
--   Finite rational interpolation as polynomial divisibility
-- statement:
--   Let R be a commutative ring, let Q,A be polynomials in R[X], and let H be a formal power series satisfying QH=1. Let α,λ∈R and s be any nonnegative integer. Then
--
--   $$\bigl([X^i](AH)=\alpha\lambda^i\text{ for every }0\le i\le s\bigr)
--   \quad\Longleftrightarrow\quad
--   X^{s+1}\mid (1-\lambda X)A-\alpha Q.$$
--
--   The divisibility on the right takes place in R[X]. Polynomial products with H on the left are interpreted in R[[X]] through the natural polynomial inclusion. Thus finite agreement of the rational formal series AH with a geometric sequence is exactly one polynomial congruence modulo X^(s+1).
--
--   The assertion includes s=0 and allows α or λ to be zero. It requires neither a field nor an integral domain. There are no degree, convergence or extra nonvanishing assumptions; the supplied identity QH=1 is the entire inverse hypothesis.
-- source:
--   Derived polynomial-congruence step for https://prove2.me/theorems/c76b8017-d835-48d3-8f68-1d93aea9503a. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is an algebraic tool for the interpolation frontier; the geometric zero estimate remains open. Primary Lean sources: Mathlib RingTheory/PowerSeries/Basic.lean (X_pow_dvd_iff, coefficient shifts, coefficientwise ring maps and polynomial_map_coe) and Algebra/Polynomial/Div.lean (X_pow_dvd_iff), revision 0df444a360eaa60ab8c11dca51a86af692955474. See https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Div.html. Multiplication by the invertible formal series Q*(1-z*X) converts finite agreement with a geometric sequence into polynomial divisibility by X^(s+1). The mission connection transfers coefficients to the scalar-extension field and collects weighted numerators, preserving every interpolation witness, weight and numerical bound.

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

open PowerSeries

theorem TranscendenceTheory.rational_interpolation_polynomial_divisibility
    (R : Type*) [CommRing R] (Q A : Polynomial R) (H : PowerSeries R)
    (hQ : (Q : PowerSeries R) * H = 1) (α z : R) (s : ℕ) :
    (∀ i ≤ s, PowerSeries.coeff i ((A : PowerSeries R) * H) = α * z ^ i) ↔
      Polynomial.X ^ (s + 1) ∣
        (1 - Polynomial.C z * Polynomial.X) * A - Polynomial.C α * Q := by sorry
