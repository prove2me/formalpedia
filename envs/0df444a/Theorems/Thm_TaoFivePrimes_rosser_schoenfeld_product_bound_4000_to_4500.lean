-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_4000_to_4500
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_4000_to_4500
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-22T20:42:14.968412+00:00
-- url     : https://prove2.me/theorems/72ccacfa-0df9-4cd1-9f4c-27b685890dee
-- statement:
--   For every real number $x$ with $4000 \le x \le 4500$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is a finite-range leg of the upper half of Theorem 23 of Rosser and Schoenfeld (p. 73, inequality (4.10)): the same bound as in the parent target, restricted to $4000 \le x \le 4500$. The range is chosen so that the statement can be verified by a finite certificate over the primes in the interval, anchored on the exact primorial certificate at $3989$ and telescoping the Euler product over the $60$ primes between $3989$ and $4493$, with the composite gaps $3990 \dots 4000$ and $4494 \dots 4500$ discharged by an interval exhaustion.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §5, p. 73, Theorem 23, inequality (4.10). https://doi.org/10.1215/ijm/1255631807 Finite range $4000 \le x \le 4500$. Companion to TaoFivePrimes.rosser_schoenfeld_product_bound_3500_to_4000 (same range family, now anchored on primorial_certificate_3989).

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_4000_to_4500 (x : ℝ) (hx : 4000 ≤ x) (hx' : x ≤ 4500) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
