-- Prove2me | Theorems.Thm_PrimalDualSubgrad_DA_eq_2_2
-- name    : PrimalDualSubgrad.DA.eq_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:35.811995+00:00
-- url     : https://prove2.me/theorems/b1ac3542-6cb2-456e-8373-3639a86f479a
-- title:
--   (2.2) — V_β(s) is nonincreasing in β
-- statement:
--   Fix a prox setting $(Q, d, \sigma, x_0)$ in a finite-dimensional normed space $E$. If $\beta_2 \ge \beta_1 > 0$, then for every $s \in E^*$
--   $$V_{\beta_2}(s) \le V_{\beta_1}(s).$$
--
--   Monotonicity in $\beta$ is what allows the scheme to increase its parameters $\beta_k$.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), §2, (2.2), p. 7

import Mathlib
import Definitions.Def_PrimalDualSubgrad_DA_ProxSetting

namespace PrimalDualSubgrad.DA

/-- (2.2), p. 7: if `β₂ ≥ β₁ > 0`, then `V_{β₂}(s) ≤ V_{β₁}(s)` for every `s ∈ E*`. -/
theorem eq_2_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (β₁ β₂ : ℝ) (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (s : StrongDual ℝ E) :
    V P β₂ s ≤ V P β₁ s := by sorry

end PrimalDualSubgrad.DA
