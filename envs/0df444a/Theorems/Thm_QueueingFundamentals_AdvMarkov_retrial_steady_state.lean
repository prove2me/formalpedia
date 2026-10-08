-- Prove2me | Theorems.Thm_QueueingFundamentals_AdvMarkov_retrial_steady_state
-- name    : QueueingFundamentals.AdvMarkov.retrial_steady_state
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T08:39:17.653269+00:00
-- url     : https://prove2.me/theorems/f4b3feaf-cc1d-4a5b-b9c9-d55c71fe476e
-- title:
--   Eq. (3.57): the stationary distribution of the M/M/1 retrial queue
-- statement:
--   Consider the $M/M/1$ retrial queue of §3.5.1: Poisson arrivals at rate $\lambda > 0$, exponential service at rate $\mu > 0$, one server, and blocked customers who wait in an orbit and retry independently at rate $\gamma > 0$ each, with no abandonment. Its state is $\{i, n\}$, with $i \in \{0,1\}$ customers in service and $n \ge 0$ in orbit. Let $\rho = \lambda/\mu$ and assume $\rho < 1$.
--
--   Define, for $n \ge 0$,
--   $$p_{0,n} = (1-\rho)^{(\lambda/\gamma)+1}\cdot\frac{\rho^n}{n!\,\gamma^n}\prod_{i=0}^{n-1}(\lambda + i\gamma), \qquad p_{1,n} = (1-\rho)^{(\lambda/\gamma)+1}\cdot\frac{\rho^{n+1}}{n!\,\gamma^n}\prod_{i=1}^{n}(\lambda + i\gamma),$$
--   with empty products equal to $1$. Then:
--
--   1. these numbers are nonnegative, $\sum_{n\ge 0}(p_{0,n} + p_{1,n}) = 1$, and they solve the rate-balance equations (3.47)–(3.49);
--   2. every nonnegative solution of (3.47)–(3.49) with total mass $1$ equals $\{p_{0,n}, p_{1,n}\}$.
--
--   In other words, (3.57) is the steady-state distribution of the retrial queue. It is one of the few retrial models whose stationary law is explicit, and all its performance measures (mean orbit size (3.58), waiting times (3.59)) follow from it.
--
--   **Formalization Note** The book states the formula after a generating-function derivation that assumes steady state; both halves of "the steady-state solution is (3.57)" — that (3.57) is a probability solution and that it is the only one — are stated explicitly. The condition $\rho < 1$ is not printed next to (3.57) but is where the derivation evaluates $(1-\rho z)^{-\lambda/\gamma}$ at $z = 1$ and the normalizing constant $(1-\rho)^{(\lambda/\gamma)+1}$ (pp.160–161). The exponent is a real power.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.161, Eq. (3.57) (model and Eqs. (3.47)–(3.49), p.159; ρ = λ/μ, p.160)

import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_Retrial

namespace QueueingFundamentals.AdvMarkov

/-- Eq. (3.57), p.161 (goal): the steady-state solution of the `M/M/1` retrial queue with
`ρ = λ/μ < 1`. The sequences (3.57) form a probability distribution solving (3.47)–(3.49), and
every such probability solution equals them. -/
theorem retrial_steady_state (lam mu gam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hgam : 0 < gam)
    (hρ1 : lam / mu < 1) :
    IsRetrialSteadyState lam mu gam (retrialP0 lam mu gam) (retrialP1 lam mu gam) ∧
      ∀ p0 p1 : ℕ → ℝ, IsRetrialSteadyState lam mu gam p0 p1 →
        p0 = retrialP0 lam mu gam ∧ p1 = retrialP1 lam mu gam := by sorry

end QueueingFundamentals.AdvMarkov
