-- Prove2me | Theorems.Thm_PrimalDualSubgrad_DA_eq_2_6
-- name    : PrimalDualSubgrad.DA.eq_2_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:35.873587+00:00
-- url     : https://prove2.me/theorems/252c1433-4739-4a54-9405-44f0306456a7
-- title:
--   (2.6) — V_β(δ) ≤ ‖δ‖²_*/(2σβ)
-- statement:
--   Fix a prox setting $(Q, d, \sigma, x_0)$ in a finite-dimensional normed space $E$ (so $d(x_0) = 0$ and $x_0$ minimizes $d$ on $Q$) and $\beta > 0$. For every $\delta \in E^*$,
--   $$V_\beta(\delta) \le \frac{1}{2\sigma\beta}\|\delta\|_*^2.$$
--
--   It bounds the first term of the telescoped sum in the proof of Theorem 1.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), §2, (2.6), p. 7

import Mathlib
import Definitions.Def_PrimalDualSubgrad_DA_ProxSetting

namespace PrimalDualSubgrad.DA

/-- (2.6), p. 7: for `β > 0` and every `δ ∈ E*`, `V_β(δ) ≤ ‖δ‖²_*/(2σβ)`. -/
theorem eq_2_6 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (β : ℝ) (hβ : 0 < β) (δ : StrongDual ℝ E) :
    V P β δ ≤ 1 / (2 * P.σ * β) * ‖δ‖ ^ 2 := by sorry

end PrimalDualSubgrad.DA
