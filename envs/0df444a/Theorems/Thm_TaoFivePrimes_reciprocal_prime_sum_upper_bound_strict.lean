-- Prove2me | Theorems.Thm_TaoFivePrimes_reciprocal_prime_sum_upper_bound_strict
-- name    : TaoFivePrimes.reciprocal_prime_sum_upper_bound_strict
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-24T13:48:38.760333+00:00
-- url     : https://prove2.me/theorems/d64844bc-df04-4df8-ac71-73bf0f4e49cb
-- title:
--   Strict explicit upper bound for the reciprocal prime sum, $x \ge 10^{8}$ (R--S 1962, (8.9))
-- statement:
--   For every real $x\ge 10^{8}$,
--
--   $$\sum_{p\le\lfloor x\rfloor,\ p\ \mathrm{prime}} \frac1p \;<\; \log\log x+\gamma+\sum_{p\ \mathrm{prime}}'\Bigl(\log\Bigl(1-\frac1p\Bigr)+\frac1p\Bigr)+\log\Bigl(1+\frac1{2\log^2 x}\Bigr),$$
--
--   where $\gamma$ is Euler's constant and the series is the usual convergent one over primes. Writing $B_1$ for Mertens' constant the series equals $B_1-\gamma$, so this is the strict form of $\sum_{p\le x}1/p<\log\log x+B_1+1/(2\log^2 x)$, i.e. the upper half of Lemma 13, inequality (8.9), of Rosser and Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), p. 86, which they state with a strict inequality.
--
--   **Why both this and the non-strict form.** The reduction of `TaoFivePrimes.rosser_schoenfeld_product_log_bound_large` has a *strict* conclusion, so at least one of its two inputs must be strict; this node supplies the strictness on the reciprocal side, while `TaoFivePrimes.mertens_tail_le_partial_sum` only removes the constant, for which a non-strict inequality suffices. The non-strict companion `TaoFivePrimes.reciprocal_prime_sum_upper_bound` is kept because it is the form in which the bound is usually quoted.
--
--   **Role.** This is the analytic half of the proof of the Mertens product bound: it follows from an explicit upper bound for the Chebyshev function by partial summation, starting from $\theta(u)\le u\,(1+\varepsilon(u))$, whose main term is $\log\log x$ with constant the same $B_1$. The published input `TaoFivePrimes.schoenfeld_psi_error_large` already supplies the needed one-sided Chebyshev bound.
--
--   **Formalization Note** Mertens' constant is kept as $\gamma+\sum_p(\log(1-1/p)+1/p)$, so no decimal approximation of $B_1$ is needed anywhere in this reduction.
-- source:
--   J. B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64--94, Lemma 13, inequality (8.9) on p. 86, stated there as a strict inequality. Companion of TaoFivePrimes.reciprocal_prime_sum_upper_bound; range threshold 10^8 matches TaoFivePrimes.schoenfeld_psi_error_large.

import Mathlib

namespace TaoFivePrimes

theorem reciprocal_prime_sum_upper_bound_strict (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) <
      Real.log (Real.log x) + Real.eulerMascheroniConstant +
        (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by sorry

end TaoFivePrimes
