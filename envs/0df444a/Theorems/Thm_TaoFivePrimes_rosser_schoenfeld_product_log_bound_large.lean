-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_log_bound_large
-- name    : TaoFivePrimes.rosser_schoenfeld_product_log_bound_large
-- status  : Open
-- author  : @chstdu
-- created : 2026-09-20T18:59:03.74731+00:00
-- url     : https://prove2.me/theorems/d5c69ba9-5a40-495b-a728-e7d11107a438
-- title:
--   Logarithmic Mertens product bound for $x \ge 10^8$ (R–S 1962, Lemma 13 + (2.7))
-- statement:
--   For every real number $x$ with $x \ge 10^8$,
--   $$\sum_{p \le x, \; p \text{ prime}} \log \frac{p}{p-1} < \gamma + \log \log x + \log\left(1 + \frac{1}{2\log^2 x}\right),$$
--   where the sum runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is the large-range leg of Rosser and Schoenfeld's proof of the Mertens product upper bound (3.29): their step (iii) (p. 87) exponentiates exactly this inequality. It packages the upper half of Lemma 13 (p. 86, inequality (8.9)) for $\sum_{p \le x} 1/p$ together with the identity (2.7) (p. 65) defining the constant $B$ and the tail estimate $S > -1.02/((x-1)\log x)$ for $S = \sum_{x < p}\{\log(1 - 1/p) + 1/p\}$ (p. 87). In the exact identity $\log \prod_{p \le x} \frac{p}{p-1} = \sum_{p \le x} \frac{1}{p} - \sum_{p \le x}\{\log(1-1/p) + 1/p\}$ the constant $B$ and the infinite tail cancel, so the statement involves only finite sums. By exponentiating both sides it is equivalent to $\prod_{p \le x} \frac{p}{p-1} < e^{\gamma}(\log x)\left(1 + \frac{1}{2\log^2 x}\right)$ for $x \ge 10^8$.
--
--   **Formalization Note.** The sum is written as `∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1))`, using the same finite set of primes as the parent target.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §8, Lemma 13, p. 86, inequality (8.9), together with (2.7), p. 65, and p. 87. https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_log_bound_large (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) <
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by sorry
end TaoFivePrimes
