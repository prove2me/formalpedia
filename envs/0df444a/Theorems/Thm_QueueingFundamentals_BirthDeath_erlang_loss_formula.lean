-- Prove2me | Theorems.Thm_QueueingFundamentals_BirthDeath_erlang_loss_formula
-- name    : QueueingFundamentals.BirthDeath.erlang_loss_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:17:19.95261+00:00
-- url     : https://prove2.me/theorems/d4d4ee4a-0620-40c5-a892-3f4960788b21
-- title:
--   Eqs. (2.52)–(2.53) — Erlang's loss formula for the M/M/c/c queue
-- statement:
--   The $M/M/c/c$ queue (Erlang loss system, $c \ge 1$ servers, no waiting room) is the birth–death process with arrival rates $\lambda_n = \lambda > 0$ for $n < c$, $\lambda_n = 0$ for $n \ge c$, and death rates $\mu_n = \min(n, c)\mu$, $\mu > 0$. Let $r = \lambda/\mu$. Then a steady-state solution exists, and $\{p_n\}$ is a steady-state solution if and only if
--   $$p_n = \frac{(\lambda/\mu)^n}{n!} \Bigm/ \Bigl(\sum_{i=0}^{c} \frac{(\lambda/\mu)^i}{i!}\Bigr) \quad (0 \le n \le c), \qquad p_n = 0 \quad (n > c).$$
--   In particular the probability of a full system is the Erlang-B formula
--   $$p_c = B(c, r) = \frac{r^c/c!}{\sum_{i=0}^{c} r^i/i!}.$$
--
--   Since arrivals are Poisson, $B(c, r)$ is also the fraction of arriving customers that are lost; it is the classical formula of telephone-trunk dimensioning.
--
--   **Formalization Note** The book's state space is $\{0, \dots, c\}$; here the process lives on $\{0, 1, 2, \dots\}$ with $\lambda_n = 0$ for $n \ge c$, which is how §2.5 sets up the truncated queue, and the statement records that the states above $c$ carry no mass.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.81–82, Eqs. (2.52), (2.53)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang

namespace QueueingFundamentals.BirthDeath

/-- Eqs. (2.52)–(2.53), pp.81–82. The `M/M/c/c` queue is the birth–death process with
`λ_n = λ` for `n < c`, `λ_n = 0` for `n ≥ c` (§2.5), and the death rates (2.30). It has a
steady-state solution, and `{p_n}` is a steady-state solution exactly when
`p_n = ((λ/μ)^n/n!) / ∑_{i=0}^{c} (λ/μ)^i/i!` for `0 ≤ n ≤ c` and `p_n = 0` for `n > c`; in
particular the probability of a full system is `p_c = B(c, r)` with `r = λ/μ`. -/
theorem erlang_loss_formula (lam mu : ℝ) (c : ℕ) (r : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) :
    (∃ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p) ∧
      (∀ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p ↔
        ((∀ n : ℕ, n ≤ c → p n = ((lam / mu) ^ n / (n.factorial : ℝ)) /
            ∑ i ∈ Finset.range (c + 1), (lam / mu) ^ i / (i.factorial : ℝ)) ∧
          ∀ n : ℕ, c < n → p n = 0)) ∧
      ∀ p : ℕ → ℝ, IsSteadyState (truncArrival lam c) (mmcDeath mu c) p →
        p c = erlangB c r := by sorry

end QueueingFundamentals.BirthDeath
