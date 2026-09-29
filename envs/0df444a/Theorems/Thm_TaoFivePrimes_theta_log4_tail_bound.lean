-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_log4_tail_bound
-- name    : TaoFivePrimes.theta_log4_tail_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:43:33.376812+00:00
-- url     : https://prove2.me/theorems/b56d2da9-59be-4cb0-9e01-b3ecc44f1964
-- title:
--   Integrating a fourth-logarithmic remainder majorant
-- statement:
--   Let $x>1$ and let $E$ be a real-valued function satisfying $|E(t)|\le100t/\log^4t$ for every $t\ge x$. Then
--
--   $$\left|\int_x^\infty E(t)\frac{\log t+1}{t^2\log^2t}\,dt\right|\le\frac{25}{\log^4x}+\frac{20}{\log^5x}.$$
--
--   This calculus comparison converts a pointwise Chebyshev error estimate into the integrated error needed in the reciprocal-prime identity.
--
--   **Formalization Note** The integral is the totalized Bochner integral. Thus no measurability hypothesis on $E$ is required: when the integrand is not integrable the integral is zero.
-- source:
--   Elementary integration of the majorant in Vanlalngaia, Explicit Mertens Sums (2017), p. 9, equation (17), https://emis.de/ft/19485: integral of 100(t log(t)^5)^(-1)+100(t log(t)^6)^(-1), using Mathlib MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'.

import Mathlib

theorem TaoFivePrimes.theta_log4_tail_bound (E : ℝ → ℝ) (x : ℝ)
    (hx : 1 < x)
    (hE : ∀ t : ℝ, x ≤ t → |E t| ≤ 100 * t / (Real.log t) ^ 4) :
    |∫ t in Set.Ioi x, E t * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)| ≤
      25 / (Real.log x) ^ 4 + 20 / (Real.log x) ^ 5 := by sorry
