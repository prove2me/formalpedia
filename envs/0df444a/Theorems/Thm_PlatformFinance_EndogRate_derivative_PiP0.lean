-- Prove2me | Theorems.Thm_PlatformFinance_EndogRate_derivative_PiP0
-- name    : PlatformFinance.EndogRate.derivative_PiP0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:42.597468+00:00
-- url     : https://prove2.me/theorems/360c1773-9061-4f18-9ab9-686df3413bcf
-- title:
--   Proof of Proposition 8, p. 43 — ∂Π^P_p(r)/∂r = G1(r)/(8(1−φ)²(1+r)²)
-- statement:
--   Let $\Pi^P_p(r)$ be the rational function (10) and
--   $$G_1(r) = c(1+r)^2\big(-a(1-\varphi)\varphi + c((1-\varphi)r_f-(2-\varphi)r-1)\big) + a^2(1-\varphi)^3(1+r_f).$$
--   For $\varphi<1$ and $r>-1$, $\Pi^P_p$ is differentiable at $r$ with
--
--   $$\frac{\partial \Pi^P_p(r)}{\partial r} = \frac{G_1(r)}{8(1-\varphi)^2(1+r)^2}.$$
--
--   Since the denominator is positive, the sign of the derivative is the sign of the cubic $G_1$; this is how the proof of Proposition 8 locates the platform's optimal rate.
-- source:
--   Huang, Lai, Wang & Xiao, Lending to Third-party Sellers with Platform Loan, SSRN 4014045, p. 43, proof of Proposition 8, display ∂Π^P_p(r)/∂r

import Mathlib
import Definitions.Def_PlatformFinance_EndogRate_Model

namespace PlatformFinance.EndogRate

/-- Proof of Proposition 8 (p. 43): `∂Π^P_p(r)/∂r = G1(r) / (8(1 - φ)²(1 + r)²)`. -/
theorem derivative_PiP0 (a φ c rf r : ℝ) (hφ1 : φ < 1) (hr : -1 < r) :
    HasDerivAt (PiP0 a φ c rf) (G1 a φ c rf r / (8 * (1 - φ) ^ 2 * (1 + r) ^ 2)) r := by sorry

end PlatformFinance.EndogRate
