-- Prove2me | Theorems.Thm_TaoFivePrimes_mertens_tail_le_partial_sum
-- name    : TaoFivePrimes.mertens_tail_le_partial_sum
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-24T13:45:59.372977+00:00
-- url     : https://prove2.me/theorems/c10a0cd0-581d-439b-b4fb-6c5ff9c5824a
-- title:
--   The Mertens tail is dominated by every finite partial sum
-- statement:
--   Write $f(p)=\log\bigl(1-\tfrac1p\bigr)+\tfrac1p$ for a prime $p$. For every real $x$,
--
--   $$\sum_{p\ \mathrm{prime}}'\; f(p)\;\le\;\sum_{p\le\lfloor x\rfloor,\ p\ \mathrm{prime}} f(p).$$
--
--   That is: the full series is dominated by each of its finite partial sums. Since $f(p)<0$ for every prime, the partial sums decrease to the sum, so this is the statement that the series converges from above.
--
--   The constant $\sum_p f(p)$ is Mertens' constant $B_1$ minus $\gamma$, numerically $B_1-\gamma=-0.3157184511\ldots$; both $B_1$ and $\gamma$ cancel when this node is combined with the reciprocal-prime upper bound, so no numerical value for either is ever needed.
--
--   **Role.** This is the *elementary* half of Rosser and Schoenfeld's proof of the Mertens product bound (3.29). Their step (iii) exponentiates the identity
--
--   $$\sum_{p\le x}\log\frac{p}{p-1}=\sum_{p\le x}\frac1p-\sum_{p\le x}f(p),$$
--
--   so the product bound follows from an upper bound for $\sum_{p\le x}1/p$ (the analytic half, `TaoFivePrimes.reciprocal_prime_sum_upper_bound`) together with this node, which removes the constant. Unlike the analytic half, this node needs no prime-counting input: it is convergence of a series plus the sign of its terms.
--
--   **Formalization Note** `Nat.primesLE x` is Mathlib's finite set of primes at most $x$, and `⌊x⌋₊` is `Nat.floor x`; the sum only depends on $\lfloor x\rfloor$.
-- source:
--   J. B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64--94, identity (2.7) on p. 65 and step (iii) of the proof of (3.29) on p. 87. The series is Mertens' constant minus Euler's constant; its convergence is classical (Mertens 1874). Stated here in the form needed by the reduction of TaoFivePrimes.rosser_schoenfeld_product_log_bound_large.

import Mathlib

namespace TaoFivePrimes

theorem mertens_tail_le_partial_sum (x : ℝ) :
    (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by sorry

end TaoFivePrimes
