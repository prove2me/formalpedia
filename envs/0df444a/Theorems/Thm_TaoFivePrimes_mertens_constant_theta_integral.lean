-- Prove2me | Theorems.Thm_TaoFivePrimes_mertens_constant_theta_integral
-- name    : TaoFivePrimes.mertens_constant_theta_integral
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T22:48:09.639426+00:00
-- url     : https://prove2.me/theorems/e63c5cbb-0d82-44b1-8430-97f986e5b232
-- title:
--   The Mertens constant as an absolutely convergent theta integral
-- statement:
--   Let $\theta(t)=\sum_{p\le t}\log p$. The real-valued function $(\theta(t)-t)(1+\log t)/(t^2\log^2t)$ is Lebesgue integrable over $(2,\infty)$, and the Mertens constant satisfies
--
--   $$\gamma+\sum_p\left(\log(1-1/p)+1/p\right)=\frac1{\log2}-\log\log2+\int_2^\infty\frac{(\theta(t)-t)(1+\log t)}{t^2\log^2t}\,dt.$$
--
--   The equality identifies the constant arising in partial summation with its Euler-product expression. Absolute integrability makes it possible to split the improper integral at any finite endpoint.
-- source:
--   R. Vanlalngaia (Ramdinmawia), Explicit Mertens Sums, INTEGERS 17 (2017), A11, p. 9, the two displayed identities for B immediately after equation (17); absolute convergence follows from standard Chebyshev remainder estimates. https://emis.de/ft/19485

import Mathlib

theorem TaoFivePrimes.mertens_constant_theta_integral :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
        (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) (Set.Ioi (2 : ℝ)) ∧
    (Real.eulerMascheroniConstant +
      ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) =
      1 / Real.log 2 - Real.log (Real.log 2) +
      ∫ t in Set.Ioi (2 : ℝ),
        (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by sorry
