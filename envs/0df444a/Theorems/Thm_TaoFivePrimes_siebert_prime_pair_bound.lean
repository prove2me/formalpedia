-- Prove2me | Theorems.Thm_TaoFivePrimes_siebert_prime_pair_bound
-- name    : TaoFivePrimes.siebert_prime_pair_bound
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T06:55:01.596773+00:00
-- url     : https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385
-- title:
--   Siebert's explicit prime-pair sieve bound
-- statement:
--   Let $x \ge 2$ and let $d > 0$ be even. The number of integers $n \le x$ for which both $n$ and $n+d$ are prime and $n+d \le x$ satisfies
--   $$\#\{\, n \le x : n,\ n+d \text{ prime},\ n+d \le x \,\} \;\le\; 8\,\mathfrak{S}_2\, \frac{x}{\log^2 x} \prod_{\substack{p \mid d \\ p > 2}} \frac{p-1}{p-2},$$
--   where $\mathfrak{S}_2$ is the twin prime constant and the product is the singular-series correction at the odd prime divisors of the shift $d$ (the product is $1$ when $d$ has no odd prime divisor). This is Siebert's dimension-two weighted sieve bound in the explicit form, with all constants written down, used in Tao's proof of Proposition 4.10.
--
--   In the formal statement the count is written as a finite sum of indicators over $\operatorname{range}(x+1)$.
-- source:
--   H. Siebert, *Montgomery's weighted sieve for dimension two*, Monatshefte für Mathematik 82 (1976), 327–336, https://doi.org/10.1007/BF01351768; as applied in T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656, https://arxiv.org/abs/1201.6656, proof of Proposition 4.10.

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators

namespace TaoFivePrimes

theorem siebert_prime_pair_bound (x d : ℕ) (hx : 2 ≤ x) (hd0 : 0 < d)
    (hd2 : 2 ∣ d) :
    (∑ n ∈ Finset.range (x + 1),
      if Nat.Prime n ∧ Nat.Prime (n + d) ∧ n + d ≤ x then (1 : ℝ) else 0) ≤
      8 * twinPrimeConstant * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 *
        ∏ p ∈ Nat.primeFactors d, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by sorry

end TaoFivePrimes
