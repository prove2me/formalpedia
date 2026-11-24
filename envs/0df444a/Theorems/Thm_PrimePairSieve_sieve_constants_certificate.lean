-- Prove2me | Theorems.Thm_PrimePairSieve_sieve_constants_certificate
-- name    : PrimePairSieve.sieve_constants_certificate
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-23T14:02:22.45383+00:00
-- url     : https://prove2.me/theorems/b2cb7da3-5535-4d4e-b75e-dfb1fa8e8a0d
-- title:
--   Certified numerical bounds for the twin-prime constant, Euler's constant and the prime logarithmic sum
-- statement:
--   ## Statement
--
--   Let $C=\mathfrak S_2 = 2\prod_{p>2}(1-\tfrac1{(p-1)^2})$ be the twin-prime singular constant, $\gamma$ Euler's constant, and
--   $$P=\sum_{p}\frac{\log p}{p(p-1)} .$$
--
--   The theorem states the certified numerical bounds
--   $$1.25\ \le\ C\ \le\ 1.3217,\qquad \gamma\ \ge\ 0.5722,\qquad P\ \ge\ 0.74 .$$
--
--   ## Meaning
--
--   These are exactly the numerical inputs consumed by the threshold-domination child `PrimePairSieve.reciprocal_base_denominator_dominates_threshold`: the sharp reciprocal expansion `PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_sharp` gives
--   $$B(z)\ge \frac{L^2+(4\gamma+4P-\log2)L-\tfrac32}{2C}-\frac{10}{3}z^{-1/3},\qquad L=\log z,$$
--   and combining the three bounds above with $\log 2\le 0.6931471808$ yields
--   $4\gamma+4P-\log2\ge 4.5556$, which drives the elementary comparison for all $z\ge40$.
--
--   ## Route
--
--   All four bounds are certified finite computations, in the style used throughout this project.
--
--   * **$C\ge1.25$.** The partial products $P(Q)=\prod_{2<p\le Q}(1-\tfrac1{(p-1)^2})$ decrease in $Q$ and $C=2\inf_Q P(Q)$. For $Q\le80$, $P(Q)\ge P(80)$, an exact rational with $P(80)\approx0.66163$; for $Q\ge80$, the primes $p$ with $80<p\le Q$ contribute factors indexed by $k=p-1\in[81,Q-1]$, so
--   $$P(Q)\ \ge\ P(80)\prod_{k=81}^{Q-1}\Bigl(1-\frac1{k^2}\Bigr)\ \ge\ P(80)\cdot\frac{80}{81}\ \ge\ 0.653.$$
--   * **$C\le1.3217$.** $C/2=\inf_Q P(Q)\le P(200)$, and the exact rational $P(200)$ satisfies $2P(200)\le1.32132$ (the product has only $46$ prime factors).
--   * **$\gamma\ge0.5722$.** Mathlib's monotone sequence $\gamma_n=H_n-\log(n+1)$ satisfies $\gamma_n<\gamma$, so it suffices that $H_{100}-\log101\ge0.5722$. Now $H_{100}$ is an exact rational and the cubic Taylor bound $\log(1+u)\le u-\tfrac{u^2}2+\tfrac{u^3}3$ gives $\log 101=\log100+\log(1+\tfrac1{100})\le4.6151213$, while $H_{100}\ge5.1873775$; hence $\gamma\ge0.572257$.
--   * **$P\ge0.74$.** The summand is positive, so the `tsum` is at least any finite partial sum; the sum is summable by comparison with $\sum p^{-3/2}$. For primes $p\le1000$ one bounds $\log p=k\log2+\log(1+u)$ with $u=p/2^k-1\le\tfrac12$ and the alternating Taylor expansion $\log(1+u)\ge u-\tfrac{u^2}2+\tfrac{u^3}3-\tfrac{u^4}4$; the resulting rational lower bound for the partial sum over the $168$ primes up to $1000$ exceeds $0.746$, while the tail beyond $1000$ is positive.
--
--   ## Reference
--
--   Numerical certificate feeding the endgame comparison for `TaoFivePrimes.siebert_prime_pair_bound`; constants as in H. Riesel and R. C. Vaughan, *On sums of primes*, Ark. Mat. **21** (1983), 46--74.
-- source:
--   Numerical certificate for the endgame constants of TaoFivePrimes.siebert_prime_pair_bound.

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators

namespace PrimePairSieve

theorem sieve_constants_certificate :
    (1.25 : ℝ) ≤ TaoFivePrimes.twinPrimeConstant ∧
      TaoFivePrimes.twinPrimeConstant ≤ 1.3217 ∧
      (0.5722 : ℝ) ≤ Real.eulerMascheroniConstant ∧
      (0.74 : ℝ) ≤
        ∑' p : Nat.Primes,
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by sorry

end PrimePairSieve
