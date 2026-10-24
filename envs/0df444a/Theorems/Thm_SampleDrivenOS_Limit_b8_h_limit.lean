-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_b8_h_limit
-- name    : SampleDrivenOS.Limit.b8_h_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:26.023984+00:00
-- url     : https://prove2.me/theorems/e361be16-852e-4a70-b405-2dc22218267a
-- title:
--   B.8, (26) — $h(p,\eta)\to\int_0^1\frac{dy}{y(1-\ln y)+1/\eta-1}$ as $p\to1$
-- statement:
--   For $p\in(0,1)$ and $\eta\in(0,1)$ let
--   $$h(p,\eta)=\frac{\sum_{i=1}^{\infty}\ln\bigl(1-\eta+\eta[(i+1)p^i-ip^{i+1}]\bigr)/(i(i+1))}{\ln p+\eta(1-p)^2/p} \qquad(26)$$
--   be the ratio of the two sides of (19), so that $h(p,\tilde\alpha(p))=1$. Then for every $\eta\in(0,1)$,
--   $$\lim_{p\to1^-}h(p,\eta)=\int_0^1\frac{dy}{y(1-\ln y)+1/\eta-1}.$$
--
--   Both numerator and denominator of $h$ tend to $0$; the limit identifies the equation for $\tilde\alpha(1)$ with the defining equation of the i.i.d. prophet constant $\alpha^*$.
--
--   **Formalization Note** The limit is one-sided ($p\to1$ from below). The denominator $\ln p+\eta(1-p)^2/p$ is negative for $p$ close to $1$, so the convention $x/0=0$ plays no role in the limit. At $y=0$ the integrand's Lean value $1/(1/\eta-1)$ is its true limit, so the interval integral is the true integral.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 35, B.8 (proof of Theorem 8), (26) and the limit computation

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- B.8 (p. 35): for `η ∈ (0, 1)`, the function `h(p, η)` of (26) tends to
`∫_0^1 1 / (y(1 - ln y) + 1/η - 1) dy` as `p → 1` from below. -/
theorem b8_h_limit (η : ℝ) (hη : η ∈ Set.Ioo (0:ℝ) 1) :
    Tendsto (fun p => hFun p η) (𝓝[<] 1)
      (𝓝 (∫ y in (0:ℝ)..1, 1 / (y * (1 - Real.log y) + 1 / η - 1))) := by sorry

end SampleDrivenOS.Limit
