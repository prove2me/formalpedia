-- Prove2me | Theorems.Thm_PrimalDualSubgrad_DA_eq_2_5
-- name    : PrimalDualSubgrad.DA.eq_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:33.398976+00:00
-- url     : https://prove2.me/theorems/ae7f4d3c-4d1f-4537-beb8-85957abea9ee
-- title:
--   (2.5) — V_β(s + δ) ≤ V_β(s) + ⟨δ, ∇V_β(s)⟩ + ‖δ‖²_*/(2σβ)
-- statement:
--   Fix a prox setting $(Q, d, \sigma, x_0)$ in a finite-dimensional normed space $E$, an argmin map $\pi$, and $\beta > 0$. For all $s, \delta \in E^*$,
--   $$V_\beta(s + \delta) \le V_\beta(s) + \langle \delta, \pi_\beta(s) - x_0\rangle + \frac{1}{2\sigma\beta}\|\delta\|_*^2,$$
--   where $\pi_\beta(s) - x_0 = \nabla V_\beta(s)$ by Lemma 1.
--
--   This upper quadratic model of $V_\beta$ is the one-step inequality of the Dual Averaging analysis.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), §2, (2.5), p. 7

import Mathlib
import Definitions.Def_PrimalDualSubgrad_DA_ProxSetting

namespace PrimalDualSubgrad.DA

/-- (2.5), p. 7: for `β > 0` and all `s, δ ∈ E*`,
`V_β(s + δ) ≤ V_β(s) + ⟨δ, ∇V_β(s)⟩ + ‖δ‖²_*/(2σβ)`, with `∇V_β(s) = π_β(s) − x0` (2.4). -/
theorem eq_2_5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) (s δ : StrongDual ℝ E) :
    V P β (s + δ) ≤ V P β s + δ (π β s - P.x0) + 1 / (2 * P.σ * β) * ‖δ‖ ^ 2 := by sorry

end PrimalDualSubgrad.DA
