-- Prove2me | Theorems.Thm_QueueingFundamentals_AdvMarkov_retrial_pgf_equations
-- name    : QueueingFundamentals.AdvMarkov.retrial_pgf_equations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T08:38:58.495292+00:00
-- url     : https://prove2.me/theorems/28b10527-7f6e-4f8c-a263-4bd9115cde4f
-- title:
--   Eqs. (3.50)–(3.52): the differential equation for the partial generating functions of the M/M/1 retrial queue
-- statement:
--   Consider the $M/M/1$ retrial queue with arrival rate $\lambda > 0$, service rate $\mu > 0$ and retrial rate $\gamma > 0$, and let $\rho = \lambda/\mu < 1$. Let $\{p_{i,n}\}$ be a steady-state solution, that is, a probability distribution on $\{0,1\}\times\{0,1,2,\dots\}$ solving the rate-balance equations (3.47)–(3.49), and let $P_0(z) = \sum_n z^n p_{0,n}$ and $P_1(z) = \sum_n z^n p_{1,n}$ be its partial generating functions.
--
--   Then for every real $z$ with $-1 < z < 1$, the function $P_0$ is differentiable at $z$ and
--   $$\begin{aligned}
--   \lambda P_0(z) + z\gamma P_0'(z) &= \mu P_1(z), && (3.50)\\
--   (\lambda+\mu)P_1(z) &= \lambda P_0(z) + \gamma P_0'(z) + \lambda z P_1(z), && (3.51)\\
--   P_0'(z) &= \frac{\lambda\rho}{\gamma(1-\rho z)}\,P_0(z). && (3.52)
--   \end{aligned}$$
--
--   Equations (3.50)–(3.51) are the balance equations transformed into generating functions; (3.52) is the separable differential equation from which the book obtains $P_0$ and $P_1$ in closed form.
--
--   **Formalization Note** The book does not state the range of $z$; the statement takes real $z \in (-1,1)$, where the power series converge and are differentiable. The hypothesis $\rho < 1$ is the condition under which a steady-state solution exists; it guarantees $1 - \rho z > 0$ on this range.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.160, Eqs. (3.50), (3.51), (3.52)

import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_Retrial

namespace QueueingFundamentals.AdvMarkov

/-- Eqs. (3.50)–(3.52), p.160: for a steady-state solution of the `M/M/1` retrial queue, the
partial generating functions `P_0`, `P_1` satisfy, for `z ∈ (−1, 1)`,
`λP_0(z) + zγP_0'(z) = μP_1(z)` (3.50), `(λ + μ)P_1(z) = λP_0(z) + γP_0'(z) + λzP_1(z)` (3.51)
and `P_0'(z) = λρ/(γ(1 − ρz)) · P_0(z)` (3.52), with `ρ = λ/μ < 1`. -/
theorem retrial_pgf_equations (lam mu gam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hgam : 0 < gam)
    (ρ : ℝ) (hρ : ρ = lam / mu) (hρ1 : ρ < 1)
    (p0 p1 : ℕ → ℝ) (hp : IsRetrialSteadyState lam mu gam p0 p1) :
    ∀ z ∈ Set.Ioo (-1 : ℝ) 1,
      DifferentiableAt ℝ (pgf p0) z ∧
      lam * pgf p0 z + z * gam * deriv (pgf p0) z = mu * pgf p1 z ∧
      (lam + mu) * pgf p1 z = lam * pgf p0 z + gam * deriv (pgf p0) z + lam * z * pgf p1 z ∧
      deriv (pgf p0) z = lam * ρ / (gam * (1 - ρ * z)) * pgf p0 z := by sorry

end QueueingFundamentals.AdvMarkov
