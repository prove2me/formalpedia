-- Prove2me | Theorems.Thm_TimeScaleAvg_eq_26
-- name    : TimeScaleAvg.eq_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:28.576007+00:00
-- url     : https://prove2.me/theorems/0c7407d5-07d2-42e0-b08c-dac656384dd9
-- title:
--   Eq. (26) — $f(y(s))-\inf_{\mathcal H}f=o(1/s^2)$
-- statement:
--   Let $f$ satisfy $(\mathcal A)$ and $\alpha>1$. For a solution $y$ of (25) on $[s_0,+\infty[$,
--
--   $$
--   f(y(s))-\inf_{\mathcal H}f=o\Bigl(\frac{1}{s^2}\Bigr)\qquad\text{as }s\to+\infty.
--   $$
--
--   This is the value rate of the rescaled dynamic, which the averaging passes on to $x$ in clause (v) of Theorem 2.
--
--   Differences from the source:
--   - reading: y(s) = z(u(s)) for a solution z of (SD), with u(s) = s²/(2(α−1)) → y any classical solution of (25) on [s₀,+∞[, with velocity ydot : ℝ to H constrained on Set.Ici s₀ only; reason: z(t) := y(√(2(α−1)t)) solves (SD) on [t₀,+∞[, so the two families of trajectories are the same
--   - reading: the time origin t₀ > 0 fixed on p.2, with s₀ given by t₀ = τ(s₀); the statement does not repeat it → hypothesis 0 < s₀; reason: a standing assumption of the paper, not repeated in the statement
--   - encoding: inf_H f → the real infimum ⨅ y, f y; reason: S ≠ ∅ makes f bounded below, so the real infimum is the true one
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eq. (26), p.5

import Mathlib
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_IsRescaledSDSolution

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Eq. (26) (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.5). For a solution `y` of (25),
`f(y(s)) - inf_H f = o(1/s²)` as `s → +∞`.

**Formalization Note.** The real infimum `⨅ z, f z` is `inf_H f` because `S ≠ ∅` makes `f` bounded
below. -/
theorem eq_26 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {α s₀ : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α) {y ydot : ℝ → H}
    (hy : IsRescaledSDSolution f α s₀ y ydot) :
    (fun s => f (y s) - ⨅ z, f z) =o[atTop] (fun s : ℝ => 1 / s ^ 2) := by sorry

end TimeScaleAvg
