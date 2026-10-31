-- Prove2me | Theorems.Thm_TimeScaleAvg_eq_32_33
-- name    : TimeScaleAvg.eq_32_33
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:42.333599+00:00
-- url     : https://prove2.me/theorems/038abf57-dd77-479d-9a31-a9a0629be9ef
-- title:
--   Eqs. (32)–(33) — $y=x+\frac{s}{\alpha-1}\dot x$ solves the rescaled steepest descent
-- statement:
--   Let $f$ satisfy $(\mathcal A)$, let $\alpha>1$, and let $x$ be a solution of (31) on $[s_0,+\infty[$ with Cauchy data $x_0=x(s_0)$, $x_1=\dot x(s_0)$. Set $y(s)=x(s)+\frac{s}{\alpha-1}\dot x(s)$. Then
--
--   $$
--   \dot y(s)+\frac{s}{\alpha-1}\nabla f(y(s))=0,\qquad y(s_0)=x_0+\frac{s_0}{\alpha-1}x_1,
--   $$
--
--   and
--
--   $$
--   \dot x(s)+\frac{\alpha-1}{s}\bigl(x(s)-y(s)\bigr)=0,\qquad x(s_0)=x_0 .
--   $$
--
--   This splits the second-order dynamic into a rescaled steepest descent followed by a linear averaging equation.
--
--   Differences from the source:
--   - reading: the solution is reached by solving (32) and then (33) → y is defined from the given x, and (32), (33) are asserted of it; reason: the page verifies that x arises this way; the Lean states that verification and asserts no existence
--   - reading: x : [s₀,+∞[ to H a solution trajectory of (31), the notion not spelled out in the statement → maps x, ẋ, ẍ : ℝ to H, each the derivative of the previous one within [s₀,+∞[ at every s ≥ s₀ (one-sided at s₀), with (31) at every s ≥ s₀; continuity of ẍ is not required; reason: p.2 speaks of classical solutions; continuity of ẍ is a consequence of the equation
--   - encoding: x defined on [s₀,+∞[ → x : ℝ to H, constrained on Set.Ici s₀ only; reason: values before s₀ enter no hypothesis and no conclusion
--   - reading: the time origin t₀ > 0 fixed on p.2, with s₀ given by t₀ = τ(s₀); the statement does not repeat it → hypothesis 0 < s₀; reason: a standing assumption of the paper, not repeated in the statement
--   - encoding: x₀, x₁ the Cauchy data of x; y = x + (s/(α−1)) ẋ → x₀ = x s₀, x₁ = xdot s₀; y = yTraj α x xdot; reason: names only
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eqs. (32)–(33), p.6

import Mathlib
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_IsImplicitHessianSolution
import Definitions.Def_TimeScaleAvg_IsRescaledSDSolution
import Definitions.Def_TimeScaleAvg_yTraj
import Definitions.Def_TimeScaleAvg_yTrajDeriv

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Eqs. (32)–(33) (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.6). Let `x` be a solution of (31)
and `y(s) = x(s) + (s/(α-1)) ẋ(s)`. Then `y` solves `ẏ(s) + (s/(α-1)) ∇f(y(s)) = 0` with
`y(s₀) = x₀ + (s₀/(α-1)) x₁`, and `ẋ(s) + ((α-1)/s)(x(s) - y(s)) = 0`.

**Formalization Note.** `x₀ = x s₀` and `x₁ = xdot s₀`, so the initial condition `x(s₀) = x₀` of
(33) holds by definition. -/
theorem eq_32_33 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {α s₀ : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α)
    {x xdot xddot : ℝ → H} (hx : IsImplicitHessianSolution f α s₀ x xdot xddot) :
    IsRescaledSDSolution f α s₀ (yTraj α x xdot) (yTrajDeriv f α x xdot) ∧
      yTraj α x xdot s₀ = x s₀ + (s₀ / (α - 1)) • xdot s₀ ∧
      ∀ s ∈ Set.Ici s₀, xdot s + ((α - 1) / s) • (x s - yTraj α x xdot s) = 0 := by sorry

end TimeScaleAvg
