-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_2000_to_1e8
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_2000_to_1e8
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-22T16:34:17.90152+00:00
-- url     : https://prove2.me/theorems/a06f56f5-36b1-4871-843b-01156ec8def0
-- statement:
--   For every real number $x$ with $2000 \le x \le 10^8$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is the analytic tail of the upper half of Theorem 23 of Rosser and Schoenfeld (p. 73, inequality (4.10)) inside the mission's range: above the finite certificates that cover $x \le 2000$, the remaining range $2000 \le x \le 10^8$ is handled by the classical analytic argument (splitting the product at $\sqrt{x}$ and bounding both parts with Rosser–Schoenfeld's estimates). Together with the finite legs below $2000$ it completes TaoFivePrimes.rosser_schoenfeld_product_bound_1500_to_1e8.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §5, p. 73, Theorem 23, inequality (4.10). https://doi.org/10.1215/ijm/1255631807 Analytic tail range $2000 \le x \le 10^8$; sibling of the finite range legs TaoFivePrimes.rosser_schoenfeld_product_bound_1500_to_2000, TaoFivePrimes.rosser_schoenfeld_product_bound_1050_to_1500 and TaoFivePrimes.rosser_schoenfeld_product_bound_700_to_1050.

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_2000_to_1e8 (x : ℝ) (hx : 2000 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
