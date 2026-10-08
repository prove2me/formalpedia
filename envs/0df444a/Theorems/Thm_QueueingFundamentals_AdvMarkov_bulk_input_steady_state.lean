-- Prove2me | Theorems.Thm_QueueingFundamentals_AdvMarkov_bulk_input_steady_state
-- name    : QueueingFundamentals.AdvMarkov.bulk_input_steady_state
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T08:38:50.508084+00:00
-- url     : https://prove2.me/theorems/3f95e5e2-2ce3-466b-98e3-9d6da671a14d
-- title:
--   Eqs. (3.1)–(3.4): generating function, idle probability and mean queue length of the M^[X]/M/1 queue
-- statement:
--   Consider the $M^{[X]}/M/1$ queue: batches arrive at rate $\lambda > 0$, each batch brings $X$ customers with $\Pr\{X = n\} = c_n$ ($n \ge 1$), and one server serves at rate $\mu > 0$. Assume $\mathrm E[X] = \sum_n n c_n < \infty$, write $\mathrm E[X^2] = \sum_n n^2 c_n$, $r = \lambda/\mu$ and $\rho = \lambda\mathrm E[X]/\mu$, and assume $\rho < 1$. Let $C(z) = \sum_{n\ge 1} c_n z^n$. Then:
--
--   1. the balance equations (3.1) have a steady-state solution $\{p_n\}$;
--   2. every steady-state solution $\{p_n\}$ of (3.1) has generating function
--   $$P(z) = \sum_{n\ge 0}p_n z^n = \frac{\mu p_0(1-z)}{\mu(1-z) - \lambda z[1 - C(z)]} \qquad (|z| \le 1,\ z \ne 1), \qquad (3.3)$$
--   and idle probability $p_0 = 1 - r\mathrm E[X] = 1 - \rho$;
--   3. if moreover $\mathrm E[X^2] < \infty$, every steady-state solution has mean number in system
--   $$L = \sum_{n\ge 0} n p_n = \frac{r(\mathrm E[X] + \mathrm E[X^2])}{2(1-\rho)} = \frac{\rho + r\mathrm E[X^2]}{2(1-\rho)}. \qquad (3.4)$$
--
--   For single arrivals ($X \equiv 1$) this reduces to the $M/M/1$ results $p_0 = 1-\rho$ and $L = \rho/(1-\rho)$.
--
--   **Formalization Note** $z$ ranges over complex numbers with $|z| \le 1$. The point $z = 1$ is excluded from (3.3), where the right-hand side is $0/0$ and the book passes to the limit $P(1) = 1$ instead. The existence of a steady state under $\rho < 1$ is the chapter's standing assumption (footnote on p.118) and is part of the statement. The mean $L$ is stated with `HasSum`, which also asserts that the series converges.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.118–119, Eqs. (3.1), (3.3), (3.4) and p_0 = 1 − rE[X] = 1 − ρ

import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_BulkInput

namespace QueueingFundamentals.AdvMarkov

/-- Eqs. (3.1), (3.3), (3.4), pp.118–119: the `M^[X]/M/1` bulk-input queue with batch arrival rate
`λ`, service rate `μ`, batch sizes `X` with `E[X] < ∞`, `r = λ/μ` and `ρ = λE[X]/μ < 1` has a
steady-state solution, and every steady-state solution has generating function
`P(z) = μp_0(1 − z)/(μ(1 − z) − λz[1 − C(z)])` for `|z| ≤ 1`, `z ≠ 1` (3.3), and
`p_0 = 1 − rE[X] = 1 − ρ`; if moreover `E[X²] < ∞`, its mean is
`L = r(E[X] + E[X²])/(2(1 − ρ)) = (ρ + rE[X²])/(2(1 − ρ))` (3.4). -/
theorem bulk_input_steady_state (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (c : ℕ → ℝ) (hc : IsBatchSizeDist c) (hc1 : Summable (fun n : ℕ => (n : ℝ) * c n))
    (EX EX2 r ρ : ℝ) (hEX : EX = ∑' n : ℕ, (n : ℝ) * c n)
    (hEX2 : EX2 = ∑' n : ℕ, (n : ℝ) ^ 2 * c n)
    (hr : r = lam / mu) (hρ : ρ = lam * EX / mu) (hρ1 : ρ < 1) :
    (∃ p : ℕ → ℝ, IsBulkInputSteadyState lam mu c p) ∧
      ∀ p : ℕ → ℝ, IsBulkInputSteadyState lam mu c p →
        (∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 →
          cpgf p z = (mu : ℂ) * (p 0 : ℂ) * (1 - z) /
            ((mu : ℂ) * (1 - z) - (lam : ℂ) * z * (1 - cpgf c z))) ∧
        p 0 = 1 - r * EX ∧ p 0 = 1 - ρ ∧
        (Summable (fun n : ℕ => (n : ℝ) ^ 2 * c n) →
          HasSum (fun n : ℕ => (n : ℝ) * p n) (r * (EX + EX2) / (2 * (1 - ρ))) ∧
          HasSum (fun n : ℕ => (n : ℝ) * p n) ((ρ + r * EX2) / (2 * (1 - ρ)))) := by sorry

end QueueingFundamentals.AdvMarkov
