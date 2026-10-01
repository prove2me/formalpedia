-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_3500_to_4000
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_3500_to_4000
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-22T20:09:03.738122+00:00
-- url     : https://prove2.me/theorems/3186ac75-a6d0-40d3-89eb-4ced3925ad98
-- statement:
--   For every real number $x$ with $3500 \le x \le 4000$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is a finite-range leg of the upper half of Theorem 23 of Rosser and Schoenfeld (p. 73, inequality (4.10)): the same bound as in the parent target, restricted to $3500 \le x \le 4000$. The range is chosen so that the statement can be verified by a finite certificate over the primes in the interval, anchored on the exact primorial certificate at $3499$ and telescoping the Euler product over the $61$ primes between $3499$ and $3989$, with the composite gap $3990 \dots 4000$ discharged by an interval exhaustion.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §5, p. 73, Theorem 23, inequality (4.10). https://doi.org/10.1215/ijm/1255631807 Finite range $3500 \le x \le 4000$. Companion to TaoFivePrimes.rosser_schoenfeld_product_bound_3000_to_3500 and TaoFivePrimes.rosser_schoenfeld_product_bound_2500_to_3000 (same range family, now anchored on primorial_certificate_3499).

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_3500_to_4000 (x : ℝ) (hx : 3500 ≤ x) (hx' : x ≤ 4000) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
