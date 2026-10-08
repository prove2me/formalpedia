-- Prove2me | Theorems.Thm_QueueingFundamentals_Transient_busy_period_density
-- name    : QueueingFundamentals.Transient.busy_period_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T08:05:21.323987+00:00
-- url     : https://prove2.me/theorems/2c466b04-178e-4cf6-8690-77c20ebf39a6
-- title:
--   §2.12 — the M/M/1 busy-period density $\sqrt{\mu/\lambda}\,e^{-(\lambda+\mu)t}I_1(2\sqrt{\lambda\mu}\,t)/t$
-- statement:
--   Let $\lambda, \mu > 0$ and let $(p_n)$ be a solution on $[0,\infty)$ of the M/M/1 equations with an absorbing barrier at $0$ ($\lambda_0 = 0$; see the busy-period Laplace-transform milestone), with $p_1(0) = 1$ and $(p_n(t))_n$ a probability distribution for every $t \ge 0$. Then the busy-period distribution function $p_0$ is differentiable at every $t > 0$, with
--
--   $$
--   p_0'(t) = \frac{\sqrt{\mu/\lambda}\; e^{-(\lambda+\mu)t}\, I_1(2\sqrt{\lambda\mu}\,t)}{t},
--   $$
--
--   where $I_1$ is the modified Bessel function of the first kind of order one.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.102, busy-period density, §2.12

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations
import Definitions.Def_QueueingFundamentals_Transient_busyPeriodDensity

namespace QueueingFundamentals.Transient

/-- The M/M/1 busy-period density (§2.12, p.102). Let `p` be a probability solution of the
absorbing-barrier equations (`λ₀ = 0`) with `p₁(0) = 1`. Then for every `t > 0`,
`p₀'(t) = √(μ/λ) e^{-(λ+μ)t} I₁(2√(λμ) t) / t`. -/
theorem busy_period_density (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (p : ℕ → ℝ → ℝ) (hsol : IsForwardSolution (busyRHS lam mu) p)
    (hprob : IsProbabilityFamily p) (hinit : ∀ n : ℕ, p n 0 = if n = 1 then 1 else 0) :
    ∀ t : ℝ, 0 < t → HasDerivAt (p 0) (busyPeriodDensity lam mu t) t := by sorry

end QueueingFundamentals.Transient
