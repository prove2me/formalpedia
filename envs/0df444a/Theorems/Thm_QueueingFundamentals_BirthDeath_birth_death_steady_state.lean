-- Prove2me | Theorems.Thm_QueueingFundamentals_BirthDeath_birth_death_steady_state
-- name    : QueueingFundamentals.BirthDeath.birth_death_steady_state
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:16:31.554335+00:00
-- url     : https://prove2.me/theorems/2fff5bfd-088b-4764-92fc-bcd90859bd8e
-- title:
--   Eqs. (2.3)–(2.4) — the steady-state solution of a birth–death process
-- statement:
--   Consider a birth–death process with birth rates $\lambda_n \ge 0$ ($n \ge 0$) and death rates $\mu_n > 0$ ($n \ge 1$). Then a steady-state solution of the balance equations (2.1) exists if and only if the series
--   $$1 + \sum_{n=1}^{\infty} \prod_{i=1}^{n} \frac{\lambda_{i-1}}{\mu_i}$$
--   converges. Moreover, a sequence $\{p_n\}$ is a steady-state solution (nonnegative, summing to one, solving (2.1)) if and only if this series converges and
--   $$p_n = p_0 \prod_{i=1}^{n} \frac{\lambda_{i-1}}{\mu_i} \quad (n \ge 0), \qquad p_0 = \Bigl(1 + \sum_{n=1}^{\infty} \prod_{i=1}^{n} \frac{\lambda_{i-1}}{\mu_i}\Bigr)^{-1}.$$
--
--   Every Markovian queue of Chapter 2 ($M/M/1$, $M/M/c$, $M/M/c/K$, $M/M/\infty$) is obtained from this result by inserting its rates.
--
--   **Formalization Note** The book writes the steady-state solution only; the statement makes both halves explicit: the displayed $\{p_n\}$ is a steady-state solution, and it is the only one. Birth rates are allowed to vanish because §2.5 applies (2.3) with $\lambda_n = 0$ for $n \ge K$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.50–52, Eqs. (2.1), (2.3), (2.4) and the existence criterion below (2.4)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

namespace QueueingFundamentals.BirthDeath

/-- Eqs. (2.1)–(2.4), pp.50–52. For a birth–death process with birth rates `λ_n ≥ 0` and death
rates `μ_n > 0` (`n ≥ 1`), a steady-state solution exists if and only if the series
`1 + ∑_{n≥1} ∏_{i=1}^{n} λ_{i-1}/μ_i` converges, and a probability vector `{p_n}` solves the
balance equations (2.1) exactly when the series converges and `p_n = p_0 ∏_{i=1}^{n} λ_{i-1}/μ_i`
(2.3) with `p_0 = (1 + ∑_{n≥1} ∏_{i=1}^{n} λ_{i-1}/μ_i)⁻¹` (2.4). -/
theorem birth_death_steady_state (lam mu : ℕ → ℝ) (hlam : ∀ n : ℕ, 0 ≤ lam n)
    (hmu : ∀ n : ℕ, 1 ≤ n → 0 < mu n) :
    ((∃ p : ℕ → ℝ, IsSteadyState lam mu p) ↔
        Summable (fun n : ℕ => bdProd lam mu (n + 1))) ∧
      ∀ p : ℕ → ℝ, IsSteadyState lam mu p ↔
        (Summable (fun n : ℕ => bdProd lam mu (n + 1)) ∧
          p 0 = (1 + ∑' n : ℕ, bdProd lam mu (n + 1))⁻¹ ∧
          ∀ n : ℕ, p n = p 0 * bdProd lam mu n) := by sorry

end QueueingFundamentals.BirthDeath
