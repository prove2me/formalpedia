-- Prove2me | Theorems.Thm_TimeScaleAvg_theorem_2
-- name    : TimeScaleAvg.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:25.568561+00:00
-- url     : https://prove2.me/theorems/c9a80c18-d2fc-4af1-9292-ccd5944e566c
-- title:
--   Theorem 2 — (31) has gradient rate $o(1/s^2)$ and converges weakly for every $\alpha>1$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, let $f:\mathcal H\to\mathbb R$ satisfy $(\mathcal A)$, let $\alpha>1$, and let $x:[s_0,+\infty[\to\mathcal H$ be a solution trajectory of
--
--   $$
--   \ddot x(s)+\frac{\alpha}{s}\dot x(s)+\nabla f\Bigl(x(s)+\frac{s}{\alpha-1}\dot x(s)\Bigr)=0.
--   $$
--
--   Then
--
--   1. $\int_{s_0}^{+\infty}s^3\bigl\|\nabla f\bigl(x(s)+\frac{s}{\alpha-1}\dot x(s)\bigr)\bigr\|^2\,ds<+\infty$;
--   2. $\bigl\|\nabla f\bigl(x(s)+\frac{s}{\alpha-1}\dot x(s)\bigr)\bigr\|=o(1/s^2)$ as $s\to+\infty$;
--   3. $\|\dot x(s)\|=o(1/s)$ as $s\to+\infty$;
--   4. $x(s)$ converges weakly as $s\to+\infty$, and its limit belongs to $S=\operatorname{argmin}f$.
--
--   If $\alpha>3$, then
--
--   5. $f(x(s))-\inf_{\mathcal H}f=o(1/s^2)$ as $s\to+\infty$.
--
--   This is the main result of the first part of the paper. Weak convergence of the trajectories holds under $\alpha>1$, in contrast with the condition $\alpha>3$ needed without Hessian-driven damping.
--
--   Differences from the source:
--   - reading: x : [s₀,+∞[ to H a solution trajectory of (31), the notion not spelled out in the statement → maps x, ẋ, ẍ : ℝ to H, each the derivative of the previous one within [s₀,+∞[ at every s ≥ s₀ (one-sided at s₀), with (31) at every s ≥ s₀; continuity of ẍ is not required; reason: p.2 speaks of classical solutions; continuity of ẍ is a consequence of the equation
--   - encoding: x defined on [s₀,+∞[ → x : ℝ to H, constrained on Set.Ici s₀ only; reason: values before s₀ enter no hypothesis and no conclusion
--   - reading: the time origin t₀ > 0 fixed on p.2, with s₀ given by t₀ = τ(s₀); the statement does not repeat it → hypothesis 0 < s₀; reason: a standing assumption of the paper, not repeated in the statement
--   - encoding: each "∫ … < +∞" → IntegrableOn of the printed integrand on Set.Ici; reason: the integrand is nonnegative and measurable, so the two conditions coincide
--   - encoding: inf_H f → the real infimum ⨅ y, f y; reason: S ≠ ∅ makes f bounded below, so the real infimum is the true one
--   - encoding: x(s) converges weakly and its limit belongs to S → ∃ p ∈ argminSet f, InertialAVD.Traj.WeakTendstoAtTop x p; reason: weak convergence is ⟨·,v⟩ convergence for every v, as written on p.8
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Theorem 2, p.6

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_IsImplicitHessianSolution

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Theorem 2 (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.6). Suppose that `f` satisfies (A), let
`x` be a solution trajectory of (31), `ẍ(s) + (α/s) ẋ(s) + ∇f(x(s) + (s/(α-1)) ẋ(s)) = 0`, and assume
`α > 1`. Then
(i) `∫_{s₀}^{+∞} s³ ‖∇f(x(s) + (s/(α-1)) ẋ(s))‖² ds < +∞`;
(ii) `‖∇f(x(s) + (s/(α-1)) ẋ(s))‖ = o(1/s²)` as `s → +∞`;
(iii) `‖ẋ(s)‖ = o(1/s)` as `s → +∞`;
(iv) `x(s)` converges weakly as `s → +∞`, and its limit belongs to `S = argmin f`.
If `α > 3`, then
(v) `f(x(s)) - inf_H f = o(1/s²)` as `s → +∞`.

**Formalization Note.** A solution is classical (`IsImplicitHessianSolution`), with values before
`s₀` playing no role; `0 < s₀` is the standing time origin of p.2. "`∫ … < +∞`" is integrability on
`[s₀, +∞[`. The real infimum `⨅ y, f y` is `inf_H f` because `S ≠ ∅` makes `f` bounded below. Only
clause (v) carries `3 < α`. -/
theorem theorem_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {α s₀ : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α)
    {x xdot xddot : ℝ → H} (hx : IsImplicitHessianSolution f α s₀ x xdot xddot) :
    IntegrableOn (fun s => s ^ 3 * ‖gradient f (x s + (s / (α - 1)) • xdot s)‖ ^ 2) (Set.Ici s₀) ∧
      (fun s => ‖gradient f (x s + (s / (α - 1)) • xdot s)‖) =o[atTop] (fun s : ℝ => 1 / s ^ 2) ∧
      (fun s => ‖xdot s‖) =o[atTop] (fun s : ℝ => 1 / s) ∧
      (∃ p ∈ argminSet f, InertialAVD.Traj.WeakTendstoAtTop x p) ∧
      (3 < α → (fun s => f (x s) - ⨅ y, f y) =o[atTop] (fun s : ℝ => 1 / s ^ 2)) := by sorry

end TimeScaleAvg
