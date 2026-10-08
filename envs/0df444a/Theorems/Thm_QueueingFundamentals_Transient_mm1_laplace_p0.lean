-- Prove2me | Theorems.Thm_QueueingFundamentals_Transient_mm1_laplace_p0
-- name    : QueueingFundamentals.Transient.mm1_laplace_p0
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:50:54.718931+00:00
-- url     : https://prove2.me/theorems/c6ff3e24-94e3-4d1d-b5b8-7ae17f92b9fc
-- title:
--   §2.11.2 — the Laplace transform $\bar p_0(s) = z_1^{i+1}/(\mu(1-z_1))$ for M/M/1
-- statement:
--   Let $\lambda, \mu > 0$ and $i \ge 0$. Let $(p_n(t))_{n \ge 0}$ be a solution on $[0,\infty)$ of the M/M/1 forward equations (2.72) with $p_n(0) = 1$ if $n = i$ and $0$ otherwise, such that $(p_n(t))_n$ is a probability distribution for every $t \ge 0$. Let $\operatorname{Re} s > 0$, let $r$ be the square root of $(\lambda+\mu+s)^2 - 4\lambda\mu$ with positive real part, and $z_1 = (\lambda+\mu+s-r)/(2\lambda)$. Then $t \mapsto e^{-st}p_0(t)$ is integrable on $(0,\infty)$ and the Laplace transform of $p_0$ is
--
--   $$
--   \bar p_0(s) = \int_0^\infty e^{-st} p_0(t)\,dt = \frac{z_1^{\,i+1}}{\mu(1-z_1)} .
--   $$
--
--   Together with (2.73) this determines the transform $\bar P(z,s)$ of the generating function, which is then inverted to obtain (2.75).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.100, formula for p̄_0(s) following Rouché's theorem, §2.11.2

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations
import Definitions.Def_QueueingFundamentals_Transient_laplace

namespace QueueingFundamentals.Transient

open MeasureTheory

/-- The Laplace transform of `p₀(t)` for the M/M/1 queue with `N(0) = i` (p.100):
for every probability solution `p` of the forward equations (2.72) with `p_n(0) = [n = i]`,
and every `s` with `Re s > 0`, `e^{-st} p₀(t)` is integrable on `(0, ∞)` and
`p̄₀(s) = z₁^{i+1} / (μ (1 - z₁))`, where `z₁ = (λ+μ+s - r)/(2λ)` and `r` is the square root of
`(λ+μ+s)² - 4λμ` with positive real part. -/
theorem mm1_laplace_p0 (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ)
    (p : ℕ → ℝ → ℝ) (hsol : IsForwardSolution (mm1RHS lam mu) p)
    (hprob : IsProbabilityFamily p) (hinit : ∀ n : ℕ, p n 0 = if n = i then 1 else 0)
    (s : ℂ) (hs : 0 < s.re) (r : ℂ)
    (hr : r ^ 2 = ((lam : ℂ) + (mu : ℂ) + s) ^ 2 - 4 * (lam : ℂ) * (mu : ℂ))
    (hr_re : 0 < r.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (p 0 t : ℂ)) (Set.Ioi 0) ∧
      laplace (p 0) s
        = (((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ))) ^ (i + 1)
          / ((mu : ℂ) * (1 - ((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ)))) := by sorry

end QueueingFundamentals.Transient
