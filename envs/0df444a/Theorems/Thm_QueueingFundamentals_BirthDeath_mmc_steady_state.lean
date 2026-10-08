-- Prove2me | Theorems.Thm_QueueingFundamentals_BirthDeath_mmc_steady_state
-- name    : QueueingFundamentals.BirthDeath.mmc_steady_state
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:16:48.610611+00:00
-- url     : https://prove2.me/theorems/a9477c02-8671-497b-b8e0-566d483ea77a
-- title:
--   Eqs. (2.31)–(2.32) — the steady-state law of the M/M/c queue
-- statement:
--   The $M/M/c$ queue ($c \ge 1$ servers) is the birth–death process with $\lambda_n = \lambda > 0$ and death rates $\mu_n = \min(n, c)\mu$, $\mu > 0$ (2.30). Let $r = \lambda/\mu$ and $\rho = r/c = \lambda/(c\mu)$. A steady-state solution exists if and only if $\rho < 1$. When $\rho < 1$, a sequence $\{p_n\}$ is a steady-state solution if and only if
--   $$p_n = \begin{cases} \dfrac{\lambda^n}{n!\,\mu^n}\,p_0 & (0 \le n < c),\\[2mm] \dfrac{\lambda^n}{c^{n-c}\,c!\,\mu^n}\,p_0 & (n \ge c),\end{cases} \qquad p_0 = \Bigl(\frac{r^c}{c!(1-\rho)} + \sum_{n=0}^{c-1} \frac{r^n}{n!}\Bigr)^{-1}.$$
--
--   These probabilities are the input to every $M/M/c$ performance measure, including the Erlang-C formula.
--
--   **Formalization Note** Both halves of "the steady-state solution is" are stated, together with the book's existence condition $\lambda/(c\mu) < 1$ (p.68).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.67–68, Eqs. (2.30), (2.31), (2.32)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

namespace QueueingFundamentals.BirthDeath

/-- Eqs. (2.31)–(2.32), pp.67–68. The `M/M/c` queue is the birth–death process with `λ_n = λ` and
the death rates (2.30). With `r = λ/μ` and `ρ = r/c`, a steady-state solution exists if and only
if `ρ = λ/(cμ) < 1`, and then `{p_n}` is a steady-state solution exactly when
`p_n = λ^n/(n! μ^n) p_0` for `0 ≤ n < c`, `p_n = λ^n/(c^{n−c} c! μ^n) p_0` for `n ≥ c`, and
`p_0 = (r^c/(c!(1 − ρ)) + ∑_{n=0}^{c−1} r^n/n!)⁻¹`. -/
theorem mmc_steady_state (lam mu : ℝ) (c : ℕ) (r ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) (hρ : ρ = r / c) :
    ((∃ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (mmcDeath mu c) p) ↔ ρ < 1) ∧
      (ρ < 1 → ∀ p : ℕ → ℝ, IsSteadyState (fun _ => lam) (mmcDeath mu c) p ↔
        ((∀ n : ℕ, p n =
            if n < c then lam ^ n / ((n.factorial : ℝ) * mu ^ n) * p 0
            else lam ^ n / ((c : ℝ) ^ (n - c) * (c.factorial : ℝ) * mu ^ n) * p 0) ∧
          p 0 = (r ^ c / ((c.factorial : ℝ) * (1 - ρ)) +
            ∑ n ∈ Finset.range c, r ^ n / (n.factorial : ℝ))⁻¹)) := by sorry

end QueueingFundamentals.BirthDeath
