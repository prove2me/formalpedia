-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_finite
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_finite
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-20T18:58:50.962256+00:00
-- url     : https://prove2.me/theorems/21a3cb00-45b6-4f7d-b7aa-66eb476ae675
-- title:
--   Mertens product upper bound (3.29), finite range $286 \le x < 700$
-- statement:
--   For every real number $x$ with $286 \le x < 700$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} (\log x)\left(1 + \frac{1}{2\log^2 x}\right),$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This theorem is the finite-range leg of Rosser and Schoenfeld's proof of the Mertens product upper bound (3.29): in their proof of Theorem 8 (p. 70) the range $x \le 16{,}000$ is disposed of by direct tabulation, and the present statement covers the part $286 \le x < 700$ of that tabulation for which no analytic substitute is available. It is provable by a finite certified computation: the left-hand side is a finite product of exact rational values, while the right-hand side can be bounded below using rational approximations to $\log x$ and $e^{\gamma}$.
--
--   **Formalization Note.** The product is written as `∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1)`, the finite set of primes at most the natural floor of $x$, and the right-hand side is `Real.exp Real.eulerMascheroniConstant * Real.log x * (1 + 1 / (2 * (Real.log x) ^ 2))`, matching the parent target's formulation.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §8, p. 70, Theorem 8, inequality (3.29), finite-range part of the proof (p. 87). https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_finite (x : ℝ) (hx : 286 ≤ x) (hx' : x < 700) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * (Real.log x) ^ 2)) := by sorry
end TaoFivePrimes
