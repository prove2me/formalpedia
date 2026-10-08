-- Prove2me | Theorems.Thm_QueueingFundamentals_BirthDeath_mm1_steady_state
-- name    : QueueingFundamentals.BirthDeath.mm1_steady_state
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:16:41.593234+00:00
-- url     : https://prove2.me/theorems/4e37ad61-dfe3-49a5-8132-932bca39803a
-- title:
--   Eq. (2.9) — the geometric steady-state law of the M/M/1 queue
-- statement:
--   The $M/M/1$ queue is the birth–death process with constant rates $\lambda_n = \lambda > 0$ and $\mu_n = \mu > 0$. Let $\rho = \lambda/\mu$. A steady-state solution of its balance equations (2.6) exists if and only if $\rho < 1$, and when $\rho < 1$ the steady-state solution is unique and geometric:
--   $$p_n = (1 - \rho)\rho^n \qquad (n \ge 0).$$
--
--   This is the basic formula from which the $M/M/1$ measures of effectiveness ($L$, $L_q$, $W$, $W_q$) are computed.
--
--   **Formalization Note** Both halves of "the steady-state solution is" are stated: under $\rho < 1$, a probability vector solves (2.6) exactly when it is the geometric law. The existence criterion $\rho < 1$ is the book's remark following (2.9).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.55, Eq. (2.9)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

namespace QueueingFundamentals.BirthDeath

/-- Eq. (2.9), p.55. The `M/M/1` queue is the birth–death process with `λ_n = λ` and `μ_n = μ`
(p.54). A steady-state solution of its balance equations (2.6) exists if and only if
`ρ = λ/μ < 1`, and then it is the geometric distribution `p_n = (1 − ρ) ρ^n`. -/
theorem mm1_steady_state (lam mu ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hρ : ρ = lam / mu) :
    ((∃ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (fun _ => mu) p) ↔ ρ < 1) ∧
      (ρ < 1 → ∀ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (fun _ => mu) p ↔
        ∀ n : ℕ, p n = (1 - ρ) * ρ ^ n) := by sorry

end QueueingFundamentals.BirthDeath
