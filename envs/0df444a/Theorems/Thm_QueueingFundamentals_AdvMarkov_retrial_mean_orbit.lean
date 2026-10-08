-- Prove2me | Theorems.Thm_QueueingFundamentals_AdvMarkov_retrial_mean_orbit
-- name    : QueueingFundamentals.AdvMarkov.retrial_mean_orbit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T08:39:18.180376+00:00
-- url     : https://prove2.me/theorems/e8320a23-5a98-49f5-aeae-dd59b0ad4347
-- title:
--   Eq. (3.58): the mean number of customers in orbit of the M/M/1 retrial queue
-- statement:
--   Consider the $M/M/1$ retrial queue with arrival rate $\lambda > 0$, service rate $\mu > 0$ and retrial rate $\gamma > 0$, and let $\rho = \lambda/\mu < 1$. For every steady-state solution $\{p_{i,n}\}$ of the rate-balance equations (3.47)–(3.49), the mean number of customers in orbit is finite and equals
--   $$L_o = \sum_{n=0}^\infty n\,(p_{0,n} + p_{1,n}) = \frac{\rho^2}{1-\rho}\cdot\frac{\mu+\gamma}{\gamma}.$$
--
--   The first factor is the mean queue length of the $M/M/1$ queue; the second, which tends to $1$ as $\gamma \to \infty$, measures the cost of retrials. With Little's law it gives the mean time in orbit (3.59).
--
--   **Formalization Note** The book defines $L_o = P'(1)$ with $P = P_0 + P_1$; the statement uses the equivalent series $\sum_n n(p_{0,n} + p_{1,n})$, and `HasSum` asserts that it converges.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.162, Eq. (3.58)

import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_Retrial

namespace QueueingFundamentals.AdvMarkov

/-- Eq. (3.58), p.162: in the `M/M/1` retrial queue with `ρ = λ/μ < 1`, the mean number of
customers in orbit is `L_o = ∑_n n (p_{0,n} + p_{1,n}) = ρ²/(1 − ρ) · (μ + γ)/γ`. -/
theorem retrial_mean_orbit (lam mu gam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hgam : 0 < gam)
    (ρ : ℝ) (hρ : ρ = lam / mu) (hρ1 : ρ < 1)
    (p0 p1 : ℕ → ℝ) (hp : IsRetrialSteadyState lam mu gam p0 p1) :
    HasSum (fun n : ℕ => (n : ℝ) * (p0 n + p1 n)) (ρ ^ 2 / (1 - ρ) * ((mu + gam) / gam)) := by sorry

end QueueingFundamentals.AdvMarkov
