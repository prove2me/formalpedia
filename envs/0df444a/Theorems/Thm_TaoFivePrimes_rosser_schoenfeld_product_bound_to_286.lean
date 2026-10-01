-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_to_286
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_to_286
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-21T16:27:23.672979+00:00
-- url     : https://prove2.me/theorems/868b1aac-ad16-4e80-bdc7-093dbd809e59
-- title:
--   Rosser–Schoenfeld (4.10), small range: product < e^γ log x + 2e^γ/√x for x < 286
-- statement:
--   For every real number $x$ with $0 < x < 286$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is the small-range leg of the upper half of Theorem 23 of Rosser and Schoenfeld (p. 73, inequality (4.10)): the same bound as in the parent target, restricted to $x < 286$, the range below which their method is replaced by direct computation. Combined with the sibling middle-range and large-range legs it disposes of the whole range $0 < x \le 10^8$ needed in their proof of the Mertens product bound (3.29); a Lean proof is a finite certification over the 61 primes $p \le 283$: the product side is evaluated exactly as a rational, $\log$ is bounded below by a $10^{-6}$-precision Taylor certificate, and $\sqrt{\ }$ by an integer overestimator, with the analytic step (monotonicity of $\log t + 2/\sqrt{t}$ in $t \ge 1$) doing the rest.
--
--   **Formalization Note.** The product is written as in the parent target, `∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1)`; $e^{\gamma}$ is `Real.exp Real.eulerMascheroniConstant` and $\sqrt{x}$ is `Real.sqrt x`.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §5, p. 73, Theorem 23, inequality (4.10) (small range $x < 286$). https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_to_286 (x : ℝ) (hx : 0 < x) (hx' : x < 286) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
