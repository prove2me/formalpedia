-- Prove2me | Theorems.Thm_QueueingFundamentals_Transient_busy_period_laplace
-- name    : QueueingFundamentals.Transient.busy_period_laplace
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:51:25.553621+00:00
-- url     : https://prove2.me/theorems/085fadff-e0dc-492f-a6d3-b001b30d9c0b
-- title:
--   §2.12 — Laplace transform of the M/M/1 busy-period distribution
-- statement:
--   Let $\lambda, \mu > 0$. Consider the M/M/1 equations with an absorbing barrier at $0$ ($\lambda_0 = 0$),
--
--   $$ p_0'(t) = \mu p_1(t), \quad p_1'(t) = -(\lambda+\mu)p_1(t) + \mu p_2(t), \quad p_n'(t) = -(\lambda+\mu)p_n(t) + \lambda p_{n-1}(t) + \mu p_{n+1}(t)\ (n\ge 2), $$
--
--   and let $(p_n)$ be a solution on $[0,\infty)$ that is a probability distribution at every $t \ge 0$, with initial size $1$: $p_1(0) = 1$. Then $p_0(t)$ is the distribution function of the busy period. For every complex $s$ with $\operatorname{Re} s > 0$, $e^{-st}p_0(t)$ is integrable on $(0,\infty)$ and
--
--   $$
--   \bar p_0(s) = \frac{2\mu}{s\big[\lambda+\mu+s+\sqrt{(\lambda+\mu+s)^2 - 4\lambda\mu}\big]},
--   $$
--
--   where the square root is the one with positive real part.
--
--   **Formalization Note** The square root is given as a hypothesis $r$ with $r^2 = (\lambda+\mu+s)^2 - 4\lambda\mu$ and $\operatorname{Re} r > 0$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.102, formula for p̄_0(s) following Eq. (2.78), §2.12

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations
import Definitions.Def_QueueingFundamentals_Transient_laplace

namespace QueueingFundamentals.Transient

open MeasureTheory

/-- The Laplace transform of the M/M/1 busy-period CDF (§2.12, p.102). Let `p` be a probability
solution of the absorbing-barrier equations (`λ₀ = 0`) with `p₁(0) = 1`, so that `p₀(t)` is the
busy-period CDF. For every `s` with `Re s > 0`, `e^{-st} p₀(t)` is integrable on `(0, ∞)` and
`p̄₀(s) = 2μ / (s [λ + μ + s + r])`, where `r` is the square root of `(λ+μ+s)² - 4λμ` with
positive real part. -/
theorem busy_period_laplace (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (p : ℕ → ℝ → ℝ) (hsol : IsForwardSolution (busyRHS lam mu) p)
    (hprob : IsProbabilityFamily p) (hinit : ∀ n : ℕ, p n 0 = if n = 1 then 1 else 0)
    (s : ℂ) (hs : 0 < s.re) (r : ℂ)
    (hr : r ^ 2 = ((lam : ℂ) + (mu : ℂ) + s) ^ 2 - 4 * (lam : ℂ) * (mu : ℂ))
    (hr_re : 0 < r.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (p 0 t : ℂ)) (Set.Ioi 0) ∧
      laplace (p 0) s = 2 * (mu : ℂ) / (s * ((lam : ℂ) + (mu : ℂ) + s + r)) := by sorry

end QueueingFundamentals.Transient
