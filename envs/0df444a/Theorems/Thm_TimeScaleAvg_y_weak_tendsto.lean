-- Prove2me | Theorems.Thm_TimeScaleAvg_y_weak_tendsto
-- name    : TimeScaleAvg.y_weak_tendsto
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:07.092107+00:00
-- url     : https://prove2.me/theorems/b6031634-3d25-4387-82fa-479091be735f
-- title:
--   Proof of Theorem 2 (iv) — $y(s)$ converges weakly to a point of $S$
-- statement:
--   Let $f$ satisfy $(\mathcal A)$ and $\alpha>1$. For a solution $y$ of (25) on $[s_0,+\infty[$, there is $x_*\in S$ such that, for every $v\in\mathcal H$,
--
--   $$
--   \langle y(s),v\rangle\to\langle x_*,v\rangle\qquad\text{as }s\to+\infty.
--   $$
--
--   This is the weak convergence that the averaging then transfers from $y$ to $x$.
--
--   Differences from the source:
--   - reading: y(s) = z(u(s)) for a solution z of (SD), with u(s) = s²/(2(α−1)) → y any classical solution of (25) on [s₀,+∞[, with velocity ydot : ℝ to H constrained on Set.Ici s₀ only; reason: z(t) := y(√(2(α−1)t)) solves (SD) on [t₀,+∞[, so the two families of trajectories are the same
--   - reading: the time origin t₀ > 0 fixed on p.2, with s₀ given by t₀ = τ(s₀); the statement does not repeat it → hypothesis 0 < s₀; reason: a standing assumption of the paper, not repeated in the statement
--   - encoding: y(s) converges weakly and its limit belongs to S → ∃ p ∈ argminSet f, InertialAVD.Traj.WeakTendstoAtTop y p; reason: weak convergence is ⟨·,v⟩ convergence for every v, as written on p.8
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, proof of Theorem 2 (iv), p.8

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_IsRescaledSDSolution

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Proof of Theorem 2 (iv) (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.8). For a solution `y` of
(25), `y(s)` converges weakly as `s → +∞` to a point of `S = argmin f`. -/
theorem y_weak_tendsto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {α s₀ : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α) {y ydot : ℝ → H}
    (hy : IsRescaledSDSolution f α s₀ y ydot) :
    ∃ p ∈ argminSet f, InertialAVD.Traj.WeakTendstoAtTop y p := by sorry

end TimeScaleAvg
