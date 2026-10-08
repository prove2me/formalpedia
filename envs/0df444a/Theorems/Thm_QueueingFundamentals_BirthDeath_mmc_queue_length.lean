-- Prove2me | Theorems.Thm_QueueingFundamentals_BirthDeath_mmc_queue_length
-- name    : QueueingFundamentals.BirthDeath.mmc_queue_length
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:16:52.066248+00:00
-- url     : https://prove2.me/theorems/d95f2d35-36b3-4094-9b2b-af7e082e9c55
-- title:
--   Eq. (2.33) — the expected queue length L_q of the M/M/c queue
-- statement:
--   In the $M/M/c$ queue with $\lambda, \mu > 0$, $c \ge 1$, $r = \lambda/\mu$ and $\rho = r/c < 1$, let $\{p_n\}$ be the steady-state solution. Then the expected number waiting in queue,
--   $$L_q = \sum_{n=c+1}^{\infty} (n - c)\,p_n,$$
--   is a convergent series with value
--   $$L_q = \Bigl(\frac{r^c \rho}{c!(1-\rho)^2}\Bigr) p_0.$$
--
--   Together with Little's formula this gives $W_q$, $W$ and $L$ of the $M/M/c$ queue, (2.34)–(2.36).
--
--   **Formalization Note** The statement asserts that the series converges to the displayed value (`HasSum`), so it cannot hold by a junk value of an infinite sum.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.68, Eq. (2.33)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

namespace QueueingFundamentals.BirthDeath

/-- Eq. (2.33), p.68. In the steady state of the `M/M/c` queue with `ρ = λ/(cμ) < 1`, the expected
queue length `L_q = ∑_{n=c+1}^{∞} (n − c) p_n` is finite and equals `(r^c ρ / (c!(1 − ρ)^2)) p_0`,
where `r = λ/μ`. -/
theorem mmc_queue_length (lam mu : ℝ) (c : ℕ) (r ρ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hc : 1 ≤ c) (hr : r = lam / mu) (hρ : ρ = r / c) (hρ1 : ρ < 1) (p : ℕ → ℝ)
    (hp : IsSteadyState (fun _ => lam) (mmcDeath mu c) p) :
    HasSum (fun n : ℕ => if c + 1 ≤ n then ((n : ℝ) - c) * p n else 0)
      (r ^ c * ρ / ((c.factorial : ℝ) * (1 - ρ) ^ 2) * p 0) := by sorry

end QueueingFundamentals.BirthDeath
