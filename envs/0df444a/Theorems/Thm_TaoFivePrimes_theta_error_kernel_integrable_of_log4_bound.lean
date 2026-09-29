-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_error_kernel_integrable_of_log4_bound
-- name    : TaoFivePrimes.theta_error_kernel_integrable_of_log4_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:56:31.643336+00:00
-- url     : https://prove2.me/theorems/92c0526e-7f5f-4f42-8615-1b8f1d8cff23
-- title:
--   Absolute integrability of the theta remainder from a fourth-log bound
-- statement:
--   Let $\theta(t)=\sum_{p\le t}\log p$. Suppose that
--
--   $$|\theta(t)-t|\le\frac{100t}{\log^4t}\qquad(t\ge70111).$$
--
--   Then the function
--
--   $$t\longmapsto\frac{(\theta(t)-t)(1+\log t)}{t^2\log^2t}$$
--
--   is Lebesgue integrable on $(2,\infty)$. This conditional calculus lemma supplies the absolute convergence required for the theta integral representation of the Mertens constant; the explicit prime-number bound remains a separate input.
-- source:
--   Elementary integrability consequence of the theta majorant in Axler, New Estimates for Some Functions Defined over Primes, INTEGERS 18 (2018), A52, Proposition 1 (2.4), applied to the kernel in Vanlalngaia, Explicit Mertens Sums (2017), p.9 equation (17). https://math.colgate.edu/~integers/s52/s52.pdf and https://emis.de/ft/19485

import Mathlib

theorem TaoFivePrimes.theta_error_kernel_integrable_of_log4_bound
    (hθ : ∀ t : ℝ, 70111 ≤ t →
      |(∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t| ≤
        100 * t / (Real.log t) ^ 4) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
        (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) (Set.Ioi (2 : ℝ)) := by sorry
