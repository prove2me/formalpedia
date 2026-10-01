-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_3500_to_1e8
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_3500_to_1e8
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-22T17:45:44.709063+00:00
-- url     : https://prove2.me/theorems/3d0cf308-4fbd-4106-8c2c-122bd82709c0
-- statement:
--   For every real number $x$ with $3500 \le x \le 10^8$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is the analytic tail of the upper half of Theorem 23 of Rosser and Schoenfeld (p. 73, inequality (4.10)) inside the mission's range: above the finite certificates that cover $x \le 3500$, the remaining range $3500 \le x \le 10^8$ is handled by the classical analytic argument (splitting the product at $\sqrt{x}$ and bounding both parts with Rosser–Schoenfeld's estimates). Together with the finite legs below $3500$ it completes TaoFivePrimes.rosser_schoenfeld_product_bound_2000_to_1e8.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §5, p. 73, Theorem 23, inequality (4.10). https://doi.org/10.1215/ijm/1255631807 Analytic tail range $3500 \le x \le 10^8$; sibling of the finite range leg TaoFivePrimes.rosser_schoenfeld_product_bound_2500_to_3500.

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_3500_to_1e8 (x : ℝ) (hx : 3500 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
