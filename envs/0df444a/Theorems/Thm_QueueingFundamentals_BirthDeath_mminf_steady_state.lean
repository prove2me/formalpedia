-- Prove2me | Theorems.Thm_QueueingFundamentals_BirthDeath_mminf_steady_state
-- name    : QueueingFundamentals.BirthDeath.mminf_steady_state
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:17:01.288924+00:00
-- url     : https://prove2.me/theorems/bf9f7c66-6daa-4cbd-8a0f-c371d2857d0c
-- title:
--   Eq. (2.57) — the Poisson steady-state law of the M/M/∞ queue
-- statement:
--   The $M/M/\infty$ queue is the birth–death process with $\lambda_n = \lambda > 0$ and $\mu_n = n\mu$, $\mu > 0$. Let $r = \lambda/\mu$. For all such $\lambda$ and $\mu$ a steady-state solution exists, and it is unique: $\{p_n\}$ is a steady-state solution if and only if
--   $$p_n = \frac{r^n e^{-r}}{n!} \qquad (n \ge 0),$$
--   the Poisson distribution with mean $r$.
--
--   Unlike the $M/M/1$ and $M/M/c$ queues, no stability condition on $\lambda/\mu$ is needed.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.84, Eq. (2.57)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

namespace QueueingFundamentals.BirthDeath

/-- Eq. (2.57), p.84. The `M/M/∞` queue is the birth–death process with `λ_n = λ` and `μ_n = nμ`.
For every `λ, μ > 0` it has a steady-state solution, and `{p_n}` is a steady-state solution
exactly when `p_n = r^n e^{−r} / n!` for all `n ≥ 0`, with `r = λ/μ` (Poisson with mean `r`). -/
theorem mminf_steady_state (lam mu r : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hr : r = lam / mu) :
    (∃ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (infDeath mu) p) ∧
      ∀ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (infDeath mu) p ↔
        ∀ n : ℕ, p n = r ^ n * Real.exp (-r) / (n.factorial : ℝ) := by sorry

end QueueingFundamentals.BirthDeath
