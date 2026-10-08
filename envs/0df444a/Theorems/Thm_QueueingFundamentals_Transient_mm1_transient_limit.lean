-- Prove2me | Theorems.Thm_QueueingFundamentals_Transient_mm1_transient_limit
-- name    : QueueingFundamentals.Transient.mm1_transient_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T08:04:34.085984+00:00
-- url     : https://prove2.me/theorems/8f911037-c315-4863-94d8-908dc4d14aa9
-- title:
--   §2.11.2 — the limit of (2.75) as $t \to \infty$
-- statement:
--   Let $\lambda, \mu > 0$, $\rho = \lambda/\mu$, let $i \ge 0$ and let $p_n(t)$ be the expression (2.75) for the M/M/1 queue started with $i$ customers. For every $n \ge 0$:
--
--   1. if $\rho < 1$, then
--   $$ \lim_{t\to\infty} p_n(t) = (1-\rho)\rho^n ; $$
--   2. if $\rho \ge 1$, then $\lim_{t\to\infty} p_n(t) = 0$.
--
--   So the transient law converges to the stationary geometric distribution exactly when $\rho < 1$, in agreement with the steady-state result (2.9).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.101, limit of Eq. (2.75), §2.11.2

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_mm1Transient

namespace QueueingFundamentals.Transient

open Filter Topology

/-- The limit of (2.75) (p.101). For `λ, μ > 0`, every initial size `i` and every `n`:
if `ρ = λ/μ < 1` then `p_n(t) → (1 - ρ) ρ^n` as `t → ∞`; if `λ/μ ≥ 1` then `p_n(t) → 0`. -/
theorem mm1_transient_limit (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) :
    (lam / mu < 1 →
        Tendsto (fun t : ℝ => mm1Transient lam mu i n t) atTop
          (𝓝 ((1 - lam / mu) * (lam / mu) ^ n))) ∧
      (1 ≤ lam / mu → Tendsto (fun t : ℝ => mm1Transient lam mu i n t) atTop (𝓝 0)) := by sorry

end QueueingFundamentals.Transient
