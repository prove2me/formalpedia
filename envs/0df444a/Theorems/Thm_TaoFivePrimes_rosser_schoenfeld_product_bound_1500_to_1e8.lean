-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_1500_to_1e8
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_1500_to_1e8
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-22T11:30:50.733473+00:00
-- url     : https://prove2.me/theorems/03c6c873-d6fb-484f-979b-4ba1273b1ee7
-- statement:
--   For every real number $x$ with $1500 < x \le 10^8$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is a finite-range leg of the upper half of Theorem 23 of Rosser and Schoenfeld (p. 73, inequality (4.10)): the same bound as in the parent target, restricted to $1500 < x \le 10^8$. The range is chosen so that the statement can be verified by a finite certificate over the primes in the interval, mirroring the accepted proof of the companion range $286 \le x < 700$ in (3.29)-form.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §5, p. 73, Theorem 23, inequality (4.10). https://doi.org/10.1215/ijm/1255631807 Range $1500 < x \le 10^8$: the analytic tail above the finite certificates.

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_1500_to_1e8 (x : ℝ) (hx : 1500 < x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
