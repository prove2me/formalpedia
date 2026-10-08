-- Prove2me | Theorems.Thm_QueueingFundamentals_BirthDeath_erlang_c_formula
-- name    : QueueingFundamentals.BirthDeath.erlang_c_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:17:22.920329+00:00
-- url     : https://prove2.me/theorems/740daa41-83b3-47c0-aab4-daf9d5e5222e
-- title:
--   Eqs. (2.37)–(2.38) — the Erlang-C probability of delay
-- statement:
--   In the $M/M/c$ queue with $\lambda, \mu > 0$, $c \ge 1$, $r = \lambda/\mu$ and $\rho = r/c < 1$, let $\{p_n\}$ be the steady-state solution, and let
--   $$W_q(0) = \sum_{n=0}^{c-1} p_n$$
--   be the steady-state probability of at most $c-1$ customers in the system (the probability of zero delay in queue). Then
--   $$W_q(0) = 1 - \frac{r^c p_0}{c!(1-\rho)}, \qquad 1 - W_q(0) = C(c, r) = \frac{r^c}{c!(1-\rho)} \Bigm/ \Bigl(\frac{r^c}{c!(1-\rho)} + \sum_{n=0}^{c-1}\frac{r^n}{n!}\Bigr).$$
--
--   The Erlang-C formula $C(c, r)$ is the standard measure of congestion in call-center staffing.
--
--   **Formalization Note** $W_q(0)$ is written as the sum of the stationary probabilities of the states $0, \dots, c-1$, which is how the book evaluates it on p.69; no waiting-time random variable is introduced.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.69, Eqs. (2.37), (2.38)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang

namespace QueueingFundamentals.BirthDeath

/-- Eqs. (2.37)–(2.38), p.69. In the steady state of the `M/M/c` queue with `r = λ/μ` and
`ρ = r/c < 1`, the probability `W_q(0) = ∑_{n=0}^{c−1} p_n` of at most `c − 1` customers in the
system equals `1 − r^c p_0 / (c!(1 − ρ))`, and its complement `1 − W_q(0)` is the Erlang-C
formula `C(c, r)`. -/
theorem erlang_c_formula (lam mu : ℝ) (c : ℕ) (r ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) (hρ : ρ = r / c) (hρ1 : ρ < 1) (p : ℕ → ℝ)
    (hp : IsSteadyState (fun _ => lam) (mmcDeath mu c) p) :
    ∑ n ∈ Finset.range c, p n = 1 - r ^ c * p 0 / ((c.factorial : ℝ) * (1 - ρ)) ∧
      1 - ∑ n ∈ Finset.range c, p n = erlangC c r := by sorry

end QueueingFundamentals.BirthDeath
