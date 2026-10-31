-- Prove2me | Theorems.Thm_TimeScaleAvg_eq_44
-- name    : TimeScaleAvg.eq_44
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:56.239627+00:00
-- url     : https://prove2.me/theorems/f1cdb0ea-7075-4744-ab4d-1117af958a9c
-- title:
--   Eq. (44) — $\int_{s_0}^{+\infty}s^3\|\nabla f(y(s))\|^2\,ds<+\infty$
-- statement:
--   Let $f$ satisfy $(\mathcal A)$ and $\alpha>1$. For a solution $y$ of (25) on $[s_0,+\infty[$,
--
--   $$
--   \int_{s_0}^{+\infty}s^3\|\nabla f(y(s))\|^2\,ds<+\infty.
--   $$
--
--   This gives clause (i) of Theorem 2 once $y$ is replaced by $x+\frac{s}{\alpha-1}\dot x$.
--
--   Differences from the source:
--   - reading: y(s) = z(u(s)) for a solution z of (SD), with u(s) = s²/(2(α−1)) → y any classical solution of (25) on [s₀,+∞[, with velocity ydot : ℝ to H constrained on Set.Ici s₀ only; reason: z(t) := y(√(2(α−1)t)) solves (SD) on [t₀,+∞[, so the two families of trajectories are the same
--   - reading: the time origin t₀ > 0 fixed on p.2, with s₀ given by t₀ = τ(s₀); the statement does not repeat it → hypothesis 0 < s₀; reason: a standing assumption of the paper, not repeated in the statement
--   - encoding: each "∫ … < +∞" → IntegrableOn of the printed integrand on Set.Ici; reason: the integrand is nonnegative and measurable, so the two conditions coincide
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eq. (44), p.7

import Mathlib
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_IsRescaledSDSolution

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Eq. (44) (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.7). For a solution `y` of (25),
`∫_{s₀}^{+∞} s³ ‖∇f(y(s))‖² ds < +∞`.

**Formalization Note.** "`∫ … < +∞`" is integrability on `[s₀, +∞[`. -/
theorem eq_44 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {α s₀ : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α) {y ydot : ℝ → H}
    (hy : IsRescaledSDSolution f α s₀ y ydot) :
    IntegrableOn (fun s => s ^ 3 * ‖gradient f (y s)‖ ^ 2) (Set.Ici s₀) := by sorry

end TimeScaleAvg
