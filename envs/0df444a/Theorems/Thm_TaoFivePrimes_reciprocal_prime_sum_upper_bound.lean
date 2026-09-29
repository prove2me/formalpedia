-- Prove2me | Theorems.Thm_TaoFivePrimes_reciprocal_prime_sum_upper_bound
-- name    : TaoFivePrimes.reciprocal_prime_sum_upper_bound
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-24T13:46:12.5144+00:00
-- url     : https://prove2.me/theorems/0c99c729-0600-44b2-9e4c-10e5012a2be3
-- title:
--   Explicit upper bound for the reciprocal prime sum, $x \ge 10^{8}$ (R--S 1962, (8.9))
-- statement:
--   For every real $x\ge 10^{8}$,
--
--   $$\sum_{p\le\lfloor x\rfloor,\ p\ \mathrm{prime}} \frac1p \;\le\; \log\log x+\gamma+\sum_{p\ \mathrm{prime}}'\Bigl(\log\Bigl(1-\frac1p\Bigr)+\frac1p\Bigr)+\log\Bigl(1+\frac1{2\log^2 x}\Bigr),$$
--
--   where $\gamma$ is Euler's constant and the series is the usual convergent one over primes.
--
--   Writing $B_1$ for Mertens' constant, the series equals $B_1-\gamma$, so this is exactly
--
--   $$\sum_{p\le x}\frac1p \;<\; \log\log x+B_1+\frac{1}{2\log^2 x},$$
--
--   which is the upper half of Lemma 13, inequality (8.9), of Rosser and Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), p. 86: the explicit form of Mertens' second theorem with the error term made numerical. The statement keeps Mertens' constant expressed as $\gamma+\sum_p(\log(1-1/p)+1/p)$ rather than as a decimal, so that it cancels exactly against `TaoFivePrimes.mertens_tail_le_partial_sum` and no numerical value of $B_1$ is required anywhere.
--
--   **Role.** This is the *analytic* half of the proof of the Mertens product bound. It follows from an explicit upper bound for the Chebyshev function by partial summation: starting from $\theta(u)\le u\,(1+\varepsilon(u))$ one gets $\sum_{p\le x}1/p=\int_{1^-}^{x}d\theta(u)/u$, whose main term is $\log\log x$ and whose constant is the same $B_1$. The published input `TaoFivePrimes.schoenfeld_psi_error_large` already supplies the needed one-sided Chebyshev bound, so this node is expected to be reachable by the same Abel-summation technique that the mission has used elsewhere.
--
--   **Formalization Note** The sum is over Mathlib's `Nat.primesLE ⌊x⌋₊`, and the series over `Nat.Primes`; the statement depends on $x$ only through $\lfloor x\rfloor$ on the left and through $\log x$ on the right.
-- source:
--   J. B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64--94, Lemma 13, inequality (8.9) on p. 86. Used in T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 4. The range threshold 10^8 matches the hypothesis of the mission's published input TaoFivePrimes.schoenfeld_psi_error_large.

import Mathlib

namespace TaoFivePrimes

theorem reciprocal_prime_sum_upper_bound (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) ≤
      Real.log (Real.log x) + Real.eulerMascheroniConstant +
        (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by sorry

end TaoFivePrimes
