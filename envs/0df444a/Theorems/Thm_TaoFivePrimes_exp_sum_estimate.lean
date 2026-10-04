-- Prove2me | Theorems.Thm_TaoFivePrimes_exp_sum_estimate
-- name    : TaoFivePrimes.exp_sum_estimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T09:03:36.523713+00:00
-- url     : https://prove2.me/theorems/19059683-718c-47c8-8d30-b3e0234abb66
-- title:
--   Theorem 1.3 — explicit estimate for the smoothed exponential sum
-- statement:
--   **Theorem 1.3 (Exponential sum estimate).** Let $x \geq 10^{20}$ be a real number, and suppose that
--
--   $$4\alpha = \frac{a}{q} + \beta$$
--
--   for an integer $a$ and a natural number $q$ with $100 \leq q \leq x/100$, $(a,q) = 1$, and $|\beta| \leq 1/q^2$. Let $q_0$ be a natural number all of whose prime factors are at most $\sqrt{x}$. Then
--
--   $$\bigl|S_{\eta_0,q_0}(x,\alpha)\bigr| \;\leq\; \left(\frac{0.14\,x}{\sqrt{q}} + \frac{0.64\,x}{\sqrt{x/q}} + 0.15\,x^{4/5}\right)\log x\,(\log x + 11.3).$$
--
--   This is the main exponential sum estimate of Tao's five-primes paper, and its durable content: the constants are small enough to be useful for $x$ between roughly $10^{30}$ and $10^{1300}$, a range in which the asymptotically superior estimates of Vinogradov, Chen–Daboussi and Ramaré carry constants that are either too large or not effective. It is the standard input to explicit Goldbach-type results, and it has since been improved by Helfgott and Platt but not superseded in method.
--
--   **On the hypotheses.** All four are load-bearing. The lower bound $x \geq 10^{20}$ is needed for the stated constants; the mission's range begins at $8.7 \times 10^{36}$, so it is satisfied there, but the estimate is false for small $x$ without it. The condition on $q_0$ is the one most easily lost, since Section 1 describes the modulus as being of minor technical importance and advises ignoring it at a first reading; it is what admits the choice $q_0 = \prod_{p \leq \sqrt{x}} p$ used at level $x$ in Section 8, and hence what connects this estimate to the sums appearing in the Fourier expression (8.11) for the weighted representation count.
--
--   Note that it is $4\alpha$, not $\alpha$, that is approximated by the rational $a/q$. As Section 1 explains, this is a consequence of allowing the modulus $q_0 = 2$, which restricts the sum to odd $n$ and saves a factor of two in the explicit constants.
--
--   **Scope.** This is (1.9) only. The refinements (1.10) for $q \leq x^{1/3}$, (1.11) for $q \geq x^{2/3}$, and (1.12) for $q \geq x^{2/3}$ with $a = \pm 1$ are separate statements and are not asserted here; they are needed for $q$ near $1$ and near $x$, where (1.9) alone is not sufficient for the argument of Section 8.
--
--   **Formalization notes.** $S_{\eta_0,q_0}$ is `smoothedExpSum eta0 q₀ x α`, using the published cutoff `eta0`. The hypothesis $\beta \in [-1/q^2, 1/q^2]$ is written as $|\beta| \leq 1/q^2$. The numerator $a$ ranges over $\mathbb{Z}$ and the coprimality condition is imposed on its absolute value. The real power $x^{4/5}$ is `Real.rpow`.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Theorem 1.3, p. 5, estimate (1.9); the hypothesis on q_0 is stated immediately before (1.9).

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes

namespace TaoFivePrimes

theorem exp_sum_estimate (x α β : ℝ) (a : ℤ) (q q₀ : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (hα : 4 * α = (a : ℝ) / q + β)
    (hβ : |β| ≤ 1 / (q : ℝ) ^ 2)
    (hq₀ : ∀ p ∈ q₀.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖smoothedExpSum eta0 q₀ x α‖ ≤
      (0.14 * x / Real.sqrt q + 0.64 * x / Real.sqrt (x / q) + 0.15 * x ^ (4 / 5 : ℝ))
        * Real.log x * (Real.log x + 11.3) := by
  sorry

end TaoFivePrimes
