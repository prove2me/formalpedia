-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_to_1e8
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_to_1e8
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-20T18:58:59.415266+00:00
-- url     : https://prove2.me/theorems/18efd75c-fdb6-4281-bd6f-a691627c4970
-- title:
--   Rosser–Schoenfeld (1962), Theorem 23 (4.10) upper half: $\prod_{p\le x} p/(p-1) < e^{\gamma}\log x + 2e^{\gamma}/\sqrt{x}$ for $0 < x \le 10^8$
-- statement:
--   For every real number $x$ with $0 < x \le 10^8$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is the upper half of Theorem 23 of Rosser and Schoenfeld (p. 73, inequality (4.10)), quoted verbatim apart from the omission of the companion lower bound $e^{\gamma}\log x < \prod_{p \le x} p/(p-1)$. In their program it disposes of the middle range of $x$ in the proof of the Mertens product bound (3.29); combined with the elementary comparison $2/\sqrt{x} \le 1/(2\log x)$, that is, $4 \log x \le \sqrt{x}$, it yields (3.29) on any range where that comparison holds. Rosser and Schoenfeld establish it by computation over the primes up to $10^8$; a Lean proof is expected to require a substantial finite certification effort.
--
--   **Formalization Note.** The product is written as in the parent target, `∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1)`; $e^{\gamma}$ is `Real.exp Real.eulerMascheroniConstant` and $\sqrt{x}$ is `Real.sqrt x`.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §5, p. 73, Theorem 23, inequality (4.10). https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_to_1e8 (x : ℝ) (hx : 0 < x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
