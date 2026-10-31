-- Prove2me | Theorems.Thm_TimeScaleAvg_eq_52
-- name    : TimeScaleAvg.eq_52
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:31.948521+00:00
-- url     : https://prove2.me/theorems/04012ff3-f492-41f4-b2a3-96b093b61cbc
-- title:
--   Eq. (52) — removal of the perturbation $\xi$
-- statement:
--   Let $f$ satisfy $(\mathcal A)$, let $\alpha>1$, let $x$ be a solution of (31) on $[s_0,+\infty[$ with $x_1=\dot x(s_0)$, and let $y=x+\frac{s}{\alpha-1}\dot x$. There is $L_f>0$ such that, with $C_f:=\frac{L_fs_0^{\alpha}}{\alpha-1}\|x_1\|$, for all $s\ge s_0$,
--
--   $$
--   f(x(s))-f\Bigl(\int_{s_0}^{s}y(u)\,d\mu_s(u)\Bigr)\le L_f\|\xi(s)\|\le\frac{C_f}{s^{\alpha-1}},
--   $$
--
--   and therefore
--
--   $$
--   f(x(s))-\inf_{\mathcal H}f\le f\Bigl(\int_{s_0}^{s}y(u)\,d\mu_s(u)\Bigr)-\inf_{\mathcal H}f+\frac{C_f}{s^{\alpha-1}}.
--   $$
--
--   This reduces the value rate at $x$ to the value rate at the $\mu_s$-average of $y$. The constant $L_f$ may depend on the trajectory.
--
--   Differences from the source:
--   - generalization: (52) and the display before it, inside the proof of clause (v), under "If α > 3" → (52) and the display before it, for every α > 1; reason: the statement with 1 < α contains the case 3 < α used by the source, and the argument never uses 3 < α
--   - reading: x : [s₀,+∞[ to H a solution trajectory of (31), the notion not spelled out in the statement → maps x, ẋ, ẍ : ℝ to H, each the derivative of the previous one within [s₀,+∞[ at every s ≥ s₀ (one-sided at s₀), with (31) at every s ≥ s₀; continuity of ẍ is not required; reason: p.2 speaks of classical solutions; continuity of ẍ is a consequence of the equation
--   - encoding: x defined on [s₀,+∞[ → x : ℝ to H, constrained on Set.Ici s₀ only; reason: values before s₀ enter no hypothesis and no conclusion
--   - reading: the time origin t₀ > 0 fixed on p.2, with s₀ given by t₀ = τ(s₀); the statement does not repeat it → hypothesis 0 < s₀; reason: a standing assumption of the paper, not repeated in the statement
--   - encoding: x₀, x₁ the Cauchy data of x; y = x + (s/(α−1)) ẋ → x₀ = x s₀, x₁ = xdot s₀; y = yTraj α x xdot; reason: names only
--   - encoding: inf_H f → the real infimum ⨅ y, f y; reason: S ≠ ∅ makes f bounded below, so the real infimum is the true one
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eq. (52) and the display before it, p.9

import Mathlib
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_IsImplicitHessianSolution
import Definitions.Def_TimeScaleAvg_yTraj
import Definitions.Def_TimeScaleAvg_muS
import Definitions.Def_TimeScaleAvg_xi

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Eq. (52) and the display before it (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.9). For a
solution `x` of (31) with `x₁ = ẋ(s₀)` and `y = x + (s/(α-1)) ẋ`, there is `L_f > 0` such that, with
`C_f := (L_f s₀^α/(α-1)) ‖x₁‖`, for all `s ≥ s₀`:
`f(x(s)) - f(∫_{s₀}^{s} y(u) dμ_s(u)) ≤ L_f ‖ξ(s)‖ ≤ C_f/s^{α-1}`, and
`f(x(s)) - inf_H f ≤ f(∫_{s₀}^{s} y(u) dμ_s(u)) - inf_H f + C_f/s^{α-1}`.

**Formalization Note.** `L_f` may depend on the trajectory, as on the page. The page derives this
inside the proof of clause (v), under `α > 3`; it is stated here for every `α > 1`. The integrals
have their real values: `y` is continuous on `[s₀, s]`, and `μ_s` is carried by that interval. -/
theorem eq_52 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {α s₀ : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α)
    {x xdot xddot : ℝ → H} (hx : IsImplicitHessianSolution f α s₀ x xdot xddot) :
    ∃ L : ℝ, 0 < L ∧ ∀ s ∈ Set.Ici s₀,
      f (x s) - f (∫ u, yTraj α x xdot u ∂(muS α s₀ s)) ≤ L * ‖xi α s₀ (xdot s₀) s‖ ∧
      L * ‖xi α s₀ (xdot s₀) s‖ ≤ (L * s₀ ^ α / (α - 1) * ‖xdot s₀‖) / s ^ (α - 1) ∧
      f (x s) - (⨅ z, f z) ≤ f (∫ u, yTraj α x xdot u ∂(muS α s₀ s)) - (⨅ z, f z) +
        (L * s₀ ^ α / (α - 1) * ‖xdot s₀‖) / s ^ (α - 1) := by sorry

end TimeScaleAvg
