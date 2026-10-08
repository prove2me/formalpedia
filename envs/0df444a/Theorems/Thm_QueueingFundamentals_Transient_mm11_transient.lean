-- Prove2me | Theorems.Thm_QueueingFundamentals_Transient_mm11_transient
-- name    : QueueingFundamentals.Transient.mm11_transient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:50:32.531988+00:00
-- url     : https://prove2.me/theorems/51520739-87fe-426c-b948-4d835e361611
-- title:
--   Eq. (2.71) — transient solution of the M/M/1/1 queue
-- statement:
--   Consider the M/M/1/1 queue (one server, no waiting room) with arrival rate $\lambda > 0$ and service rate $\mu > 0$, and let $p_0(t), p_1(t)$ be real functions with $p_0(0) + p_1(0) = 1$. Then $(p_0, p_1)$ solves the equations (2.70),
--
--   $$ p_1'(t) = -\mu p_1(t) + \lambda p_0(t), \qquad p_0'(t) = -\lambda p_0(t) + \mu p_1(t), $$
--
--   on $[0,\infty)$ if and only if for every $t \ge 0$
--
--   $$
--   p_1(t) = \frac{\lambda}{\lambda+\mu}\big(1 - e^{-(\lambda+\mu)t}\big) + p_1(0)e^{-(\lambda+\mu)t}, \qquad
--   p_0(t) = \frac{\mu}{\lambda+\mu}\big(1 - e^{-(\lambda+\mu)t}\big) + p_0(0)e^{-(\lambda+\mu)t}.
--   $$
--
--   This is the simplest transient queueing law; letting $t \to \infty$ gives the stationary distribution $p_1 = \rho/(\rho+1)$, $p_0 = 1/(\rho+1)$.
--
--   **Formalization Note** The book uses $p_0(t) + p_1(t) = 1$ for all $t$; the statement assumes it only at $t = 0$ (for solutions of (2.70) the sum is constant). The "if and only if" packages both halves: the formulas solve (2.70), and they are the only solution.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.98, Eq. (2.71) (equations (2.70) on p.97)

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations

namespace QueueingFundamentals.Transient

/-- (2.71): transient solution of the M/M/1/1 queue. For a pair `(p₀, p₁)` with
`p₀(0) + p₁(0) = 1`, the equations (2.70) hold on `[0, ∞)` if and only if, for all `t ≥ 0`,
`p₁(t) = λ/(λ+μ) (1 - e^{-(λ+μ)t}) + p₁(0) e^{-(λ+μ)t}` and
`p₀(t) = μ/(λ+μ) (1 - e^{-(λ+μ)t}) + p₀(0) e^{-(λ+μ)t}`. -/
theorem mm11_transient (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (p : Fin 2 → ℝ → ℝ)
    (hsum : p 0 0 + p 1 0 = 1) :
    IsForwardSolution (mm11RHS lam mu) p ↔
      ∀ t : ℝ, 0 ≤ t →
        p 1 t = lam / (lam + mu) * (1 - Real.exp (-(lam + mu) * t))
            + p 1 0 * Real.exp (-(lam + mu) * t) ∧
        p 0 t = mu / (lam + mu) * (1 - Real.exp (-(lam + mu) * t))
            + p 0 0 * Real.exp (-(lam + mu) * t) := by sorry

end QueueingFundamentals.Transient
