-- Prove2me | Theorems.Thm_TimeScaleAvg_eq_after_50
-- name    : TimeScaleAvg.eq_after_50
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:52.211878+00:00
-- url     : https://prove2.me/theorems/07c65c8a-ec71-4e3a-bedd-eb59fced3a47
-- title:
--   Display after (50) — $\dot x$ in terms of $\dot y$
-- statement:
--   Let $f$ satisfy $(\mathcal A)$, let $\alpha>1$, let $x$ be a solution of (31) on $[s_0,+\infty[$ with $x_1=\dot x(s_0)$, and let $y=x+\frac{s}{\alpha-1}\dot x$. For every $s\ge s_0$,
--
--   $$
--   \dot x(s)=\frac{\alpha-1}{s^{\alpha}}\int_{s_0}^{s}u^{\alpha-1}\dot y(u)\,du+\frac{s_0^{\alpha}}{s^{\alpha}}x_1.
--   $$
--
--   This expresses $\dot x$ through the quantity whose decay is given by (47).
--
--   Differences from the source:
--   - encoding: ẏ → yTrajDeriv f α x xdot, the right-hand side of (32); reason: eq_32_33 states that it is the derivative of y; this avoids taking that fact as a hypothesis
--   - reading: x : [s₀,+∞[ to H a solution trajectory of (31), the notion not spelled out in the statement → maps x, ẋ, ẍ : ℝ to H, each the derivative of the previous one within [s₀,+∞[ at every s ≥ s₀ (one-sided at s₀), with (31) at every s ≥ s₀; continuity of ẍ is not required; reason: p.2 speaks of classical solutions; continuity of ẍ is a consequence of the equation
--   - encoding: x defined on [s₀,+∞[ → x : ℝ to H, constrained on Set.Ici s₀ only; reason: values before s₀ enter no hypothesis and no conclusion
--   - reading: the time origin t₀ > 0 fixed on p.2, with s₀ given by t₀ = τ(s₀); the statement does not repeat it → hypothesis 0 < s₀; reason: a standing assumption of the paper, not repeated in the statement
--   - encoding: x₀, x₁ the Cauchy data of x; y = x + (s/(α−1)) ẋ → x₀ = x s₀, x₁ = xdot s₀; y = yTraj α x xdot; reason: names only
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, display after (50), p.8

import Mathlib
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_IsImplicitHessianSolution
import Definitions.Def_TimeScaleAvg_yTrajDeriv

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- The display after (50) (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.8). For a solution `x` of
(31) with `x₁ = ẋ(s₀)` and `y = x + (s/(α-1)) ẋ`, at every `s ≥ s₀`,
`ẋ(s) = ((α-1)/s^α) ∫_{s₀}^{s} u^{α-1} ẏ(u) du + (s₀^α/s^α) x₁`.

**Formalization Note.** `ẏ` is `yTrajDeriv f α x xdot`, the right-hand side of (32), which
`TimeScaleAvg.eq_32_33` shows to be the derivative of `y`. It is continuous on `[s₀, +∞[` under (A),
so the integral has its real value. -/
theorem eq_after_50 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {α s₀ : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α)
    {x xdot xddot : ℝ → H} (hx : IsImplicitHessianSolution f α s₀ x xdot xddot) :
    ∀ s ∈ Set.Ici s₀,
      xdot s = ((α - 1) / s ^ α) • (∫ u in s₀..s, u ^ (α - 1) • yTrajDeriv f α x xdot u) +
        (s₀ ^ α / s ^ α) • xdot s₀ := by sorry

end TimeScaleAvg
