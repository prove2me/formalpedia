-- Prove2me | Theorems.Thm_RV27_interval_goldbach_bound
-- name    : RV27.interval_goldbach_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-06T15:07:14.979095+00:00
-- url     : https://prove2.me/theorems/615aa310-e650-4203-b2d6-7695557e1c8e
-- title:
--   Siebert-type upper bound for Goldbach representations with one prime in a short interval
-- statement:
--   Let $s$ be a positive even integer, $a \ge 0$ and $L \ge 25600$. The number of primes $p \in (a, a+L]$ with $p < s$ and $s - p$ prime satisfies
--   $$\#\{a < p \le a + L : p,\ s-p \text{ prime}\} \le \frac{8\,\mathfrak S_2\,K(s)\,L}{\log^2 L} + \frac{\sqrt L}{2} + 2, \qquad K(s) = \prod_{p \mid s,\ p > 2} \frac{p-1}{p-2},$$
--   where $\mathfrak S_2 = 2\prod_{p>2}(1 - (p-1)^{-2})$ is the twin prime constant (`TaoFivePrimes.twinPrimeConstant`). This is the short-interval form of Siebert's prime-pair bound in the Goldbach setting, as used by Riesel and Vaughan for the upper bound in their Lemma 9: the sieve level is $z = \sqrt L/4$, and the error $\sqrt L/2 + 2$ accounts for the primes $p \le z$ or $s - p \le z$ that the sieve does not see.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Ark. Mat. 21 (1983) 45–74, Lemma 5 (with A = 0) and its use in the proof of Lemma 9 (§7); H. Siebert, Montgomery's weighted sieve for dimension two, Monatsh. Math. 82 (1976) 327–336.

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
open scoped BigOperators
set_option autoImplicit false

theorem RV27.interval_goldbach_bound (s a L : ℕ) (hs : Even s) (hs0 : 0 < s) (hL : 25600 ≤ L) :
    (((Finset.Ioc a (a + L)).filter (fun p => p.Prime ∧ p < s ∧ (s - p).Prime)).card : ℝ) ≤
      8 * TaoFivePrimes.twinPrimeConstant *
        (∏ p ∈ s.primeFactors, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1) * (L : ℝ) /
        (Real.log (L : ℝ)) ^ 2 + √(L : ℝ) / 2 + 2 := by sorry
