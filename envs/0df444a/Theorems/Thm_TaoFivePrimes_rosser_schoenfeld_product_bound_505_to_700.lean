-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_505_to_700
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_505_to_700
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-22T11:30:30.810696+00:00
-- url     : https://prove2.me/theorems/609103be-866c-4236-a65d-020e77535b2a
-- statement:
--   For every real number $x$ with $505 \le x < 700$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is a finite-range leg of the upper half of Theorem 23 of Rosser and Schoenfeld (p. 73, inequality (4.10)): the same bound as in the parent target, restricted to $505 \le x < 700$. The range is chosen so that the statement can be verified by a finite certificate over the primes in the interval, mirroring the accepted proof of the companion range $286 \le x < 700$ in (3.29)-form.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §5, p. 73, Theorem 23, inequality (4.10). https://doi.org/10.1215/ijm/1255631807 Finite range $505 \le x < 700$. Companion to TaoFivePrimes.rosser_schoenfeld_product_bound_finite ((3.29)-form, same range family).

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_505_to_700 (x : ℝ) (hx : 505 ≤ x) (hx' : x < 700) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
