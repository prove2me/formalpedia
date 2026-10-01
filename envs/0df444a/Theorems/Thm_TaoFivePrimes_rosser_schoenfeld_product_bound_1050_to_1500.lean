-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_1050_to_1500
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_1050_to_1500
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-22T16:20:25.322995+00:00
-- url     : https://prove2.me/theorems/e287daae-977b-4b7e-b87c-cadef9a8e32a
-- statement:
--   For every real number $x$ with $1050 \le x \le 1500$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is a finite-range leg of the upper half of Theorem 23 of Rosser and Schoenfeld (p. 73, inequality (4.10)): the same bound as in the parent target, restricted to $1050 \le x \le 1500$. The range is chosen so that the statement can be verified by a finite certificate over the primes in the interval, anchored on the accepted exact primorial certificate at $1049$ and telescoping the Euler product over the $63$ primes between $1049$ and $1499$.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §5, p. 73, Theorem 23, inequality (4.10). https://doi.org/10.1215/ijm/1255631807 Finite range $1050 \le x \le 1500$. Companion to TaoFivePrimes.rosser_schoenfeld_product_bound_505_to_700 and TaoFivePrimes.rosser_schoenfeld_product_bound_700_to_1050 (same range family).

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_1050_to_1500 (x : ℝ) (hx : 1050 ≤ x) (hx' : x ≤ 1500) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
