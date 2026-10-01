-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_700_to_1500
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_700_to_1500
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-22T11:30:51.142774+00:00
-- url     : https://prove2.me/theorems/004a41c4-151f-4216-9cd1-f57289d44049
-- statement:
--   For every real number $x$ with $700 \le x \le 1500$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is a finite-range leg of the upper half of Theorem 23 of Rosser and Schoenfeld (p. 73, inequality (4.10)): the same bound as in the parent target, restricted to $700 \le x \le 1500$. The range is chosen so that the statement can be verified by a finite certificate over the primes in the interval, mirroring the accepted proof of the companion range $286 \le x < 700$ in (3.29)-form.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §5, p. 73, Theorem 23, inequality (4.10). https://doi.org/10.1215/ijm/1255631807 Finite range $700 \le x \le 1500$; the next leg above the (3.29) window.

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_700_to_1500 (x : ℝ) (hx : 700 ≤ x) (hx' : x ≤ 1500) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
