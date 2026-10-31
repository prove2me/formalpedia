-- Prove2me | Theorems.Thm_TimeScaleAvg_eq_39
-- name    : TimeScaleAvg.eq_39
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:53.812611+00:00
-- url     : https://prove2.me/theorems/1f00b765-c0d6-4826-9162-70bd6b11e499
-- title:
--   Eqs. (37)–(39) — $x$ is a $\mu_s$-average of $y$ plus a perturbation
-- statement:
--   Let $f$ satisfy $(\mathcal A)$, let $\alpha>1$, let $x$ be a solution of (31) on $[s_0,+\infty[$ with $x_0=x(s_0)$, $x_1=\dot x(s_0)$, and let $y=x+\frac{s}{\alpha-1}\dot x$. For every $s\ge s_0$, the measure $\mu_s$ is a probability measure and
--
--   $$
--   x(s)=\frac{s_0^{\alpha-1}}{s^{\alpha-1}}x_0+\frac{\alpha-1}{s^{\alpha-1}}\int_{s_0}^{s}u^{\alpha-2}y(u)\,du
--   =\frac{s_0^{\alpha-1}}{s^{\alpha-1}}y(s_0)+\frac{\alpha-1}{s^{\alpha-1}}\int_{s_0}^{s}u^{\alpha-2}y(u)\,du-\frac{s_0^{\alpha}}{(\alpha-1)s^{\alpha-1}}x_1,
--   $$
--
--   so that
--
--   $$
--   x(s)=\int_{s_0}^{s}y(u)\,d\mu_s(u)+\xi(s).
--   $$
--
--   This identifies $x$ as an average of $y$, up to the perturbation $\xi$.
--
--   Differences from the source:
--   - encoding: μ_s a positive Radon measure on [s₀,s] of total mass 1 (p.9) → muS is a Measure ℝ carried by [s₀,s], with IsProbabilityMeasure joined to (37)–(39) in one conclusion; reason: the p.9 fact and the identities concern the same measure
--   - reading: x : [s₀,+∞[ to H a solution trajectory of (31), the notion not spelled out in the statement → maps x, ẋ, ẍ : ℝ to H, each the derivative of the previous one within [s₀,+∞[ at every s ≥ s₀ (one-sided at s₀), with (31) at every s ≥ s₀; continuity of ẍ is not required; reason: p.2 speaks of classical solutions; continuity of ẍ is a consequence of the equation
--   - encoding: x defined on [s₀,+∞[ → x : ℝ to H, constrained on Set.Ici s₀ only; reason: values before s₀ enter no hypothesis and no conclusion
--   - reading: the time origin t₀ > 0 fixed on p.2, with s₀ given by t₀ = τ(s₀); the statement does not repeat it → hypothesis 0 < s₀; reason: a standing assumption of the paper, not repeated in the statement
--   - encoding: x₀, x₁ the Cauchy data of x; y = x + (s/(α−1)) ẋ → x₀ = x s₀, x₁ = xdot s₀; y = yTraj α x xdot; reason: names only
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eqs. (37)–(39), pp.6–7; total mass of $\mu_s$, p.9

import Mathlib
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_IsImplicitHessianSolution
import Definitions.Def_TimeScaleAvg_yTraj
import Definitions.Def_TimeScaleAvg_muS
import Definitions.Def_TimeScaleAvg_xi

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Eqs. (37)–(39) (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, pp.6–7). For a solution `x` of (31)
with `x₀ = x s₀`, `x₁ = ẋ(s₀)` and `y = x + (s/(α-1)) ẋ`, at every `s ≥ s₀`: the measure `μ_s` is a
probability measure ("whose total mass is equal to 1", p.9), and
`x(s) = (s₀^{α-1}/s^{α-1}) x₀ + ((α-1)/s^{α-1}) ∫_{s₀}^{s} u^{α-2} y(u) du` (37),
`x(s) = (s₀^{α-1}/s^{α-1}) y(s₀) + ((α-1)/s^{α-1}) ∫_{s₀}^{s} u^{α-2} y(u) du
  - (s₀^α/((α-1) s^{α-1})) x₁` (38), and `x(s) = ∫_{s₀}^{s} y(u) dμ_s(u) + ξ(s)` (39).

**Formalization Note.** All the integrands are continuous on `[s₀, s]`: `y` has a derivative at
every point of `[s₀, +∞[`, and `u ≥ s₀ > 0`. So the Bochner integrals have their real values. -/
theorem eq_39 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {α s₀ : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α)
    {x xdot xddot : ℝ → H} (hx : IsImplicitHessianSolution f α s₀ x xdot xddot) :
    ∀ s ∈ Set.Ici s₀,
      IsProbabilityMeasure (muS α s₀ s) ∧
      x s = (s₀ ^ (α - 1) / s ^ (α - 1)) • x s₀ +
        ((α - 1) / s ^ (α - 1)) • ∫ u in s₀..s, u ^ (α - 2) • yTraj α x xdot u ∧
      x s = (s₀ ^ (α - 1) / s ^ (α - 1)) • yTraj α x xdot s₀ +
        ((α - 1) / s ^ (α - 1)) • (∫ u in s₀..s, u ^ (α - 2) • yTraj α x xdot u) -
        (s₀ ^ α / ((α - 1) * s ^ (α - 1))) • xdot s₀ ∧
      x s = (∫ u, yTraj α x xdot u ∂(muS α s₀ s)) + xi α s₀ (xdot s₀) s := by sorry

end TimeScaleAvg
