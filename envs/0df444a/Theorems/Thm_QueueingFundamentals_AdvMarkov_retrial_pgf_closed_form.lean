-- Prove2me | Theorems.Thm_QueueingFundamentals_AdvMarkov_retrial_pgf_closed_form
-- name    : QueueingFundamentals.AdvMarkov.retrial_pgf_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T08:38:51.793348+00:00
-- url     : https://prove2.me/theorems/277d7470-81b2-49df-91e4-cbcd2bfb53e2
-- title:
--   Eq. (3.55): the partial generating functions of the M/M/1 retrial queue in closed form
-- statement:
--   Consider the $M/M/1$ retrial queue with arrival rate $\lambda > 0$, service rate $\mu > 0$ and retrial rate $\gamma > 0$, and let $\rho = \lambda/\mu < 1$. Let $\{p_{i,n}\}$ be a steady-state solution of the rate-balance equations (3.47)–(3.49), with partial generating functions $P_0(z) = \sum_n z^n p_{0,n}$ and $P_1(z) = \sum_n z^n p_{1,n}$. Then for every real $z$ with $-1 \le z \le 1$,
--   $$P_0(z) = (1-\rho z)\left(\frac{1-\rho}{1-\rho z}\right)^{(\lambda/\gamma)+1}, \qquad P_1(z) = \rho\left(\frac{1-\rho}{1-\rho z}\right)^{(\lambda/\gamma)+1}.$$
--
--   At $z = 1$ this gives $P_1(1) = \sum_n p_{1,n} = \rho$, the fraction of time the server is busy. Expanding these functions in powers of $z$ yields the steady-state probabilities (3.57).
--
--   **Formalization Note** The book does not state the range of $z$; the statement takes real $z \in [-1,1]$, where the series converge absolutely and $1 - \rho z > 0$. The power $(\lambda/\gamma)+1$ is a real power of a positive number.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.161, Eq. (3.55)

import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_Retrial

namespace QueueingFundamentals.AdvMarkov

/-- Eq. (3.55), p.161: for a steady-state solution of the `M/M/1` retrial queue with
`ρ = λ/μ < 1`, the partial generating functions are, for `z ∈ [−1, 1]`,
`P_0(z) = (1 − ρz)((1 − ρ)/(1 − ρz))^{(λ/γ)+1}` and `P_1(z) = ρ((1 − ρ)/(1 − ρz))^{(λ/γ)+1}`. -/
theorem retrial_pgf_closed_form (lam mu gam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hgam : 0 < gam)
    (ρ : ℝ) (hρ : ρ = lam / mu) (hρ1 : ρ < 1)
    (p0 p1 : ℕ → ℝ) (hp : IsRetrialSteadyState lam mu gam p0 p1) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      pgf p0 z = (1 - ρ * z) * ((1 - ρ) / (1 - ρ * z)) ^ (lam / gam + 1) ∧
      pgf p1 z = ρ * ((1 - ρ) / (1 - ρ * z)) ^ (lam / gam + 1) := by sorry

end QueueingFundamentals.AdvMarkov
