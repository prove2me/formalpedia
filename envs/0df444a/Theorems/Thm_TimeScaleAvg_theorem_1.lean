-- Prove2me | Theorems.Thm_TimeScaleAvg_theorem_1
-- name    : TimeScaleAvg.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:43.254974+00:00
-- url     : https://prove2.me/theorems/c936231b-a9c6-4a55-8540-ea8a98709322
-- title:
--   Theorem 1 — rates and weak convergence for the perturbed steepest descent
-- statement:
--   Let $f$ satisfy $(\mathcal A)$, and let $z$ be a (strong) solution on $[t_0,+\infty[$ of
--
--   $$
--   \dot z(t)+\nabla f(z(t))=g(t),
--   $$
--
--   where $\int_{t_0}^{+\infty}\|g(t)\|\,dt<+\infty$ and $\int_{t_0}^{+\infty}t\|g(t)\|^2\,dt<+\infty$. Then
--
--   1. $\int_{t_0}^{+\infty}t\|\dot z(t)\|^2\,dt<+\infty$;
--   2. $\int_{t_0}^{+\infty}t\|\nabla f(z(t))\|^2\,dt<+\infty$;
--   3. $\int_{t_0}^{+\infty}\bigl(f(z(t))-\inf_{\mathcal H}f\bigr)\,dt<+\infty$;
--   4. $f(z(t))-\inf_{\mathcal H}f=o(1/t)$ as $t\to+\infty$;
--   5. $z(t)$ converges weakly as $t\to+\infty$, and its limit belongs to $S=\operatorname{argmin}f$.
--
--   If moreover $\int_{t_0}^{+\infty}t^2\|g(t)\|^2\,dt<+\infty$, then
--
--   6. $\|\nabla f(z(t))\|=o(1/t)$ as $t\to+\infty$.
--
--   This is the steepest-descent input from which all the fast rates of the paper are derived.
--
--   Differences from the source:
--   - generalization: z : [t₀,+∞[ to H a solution trajectory of (6), the notion not spelled out in the statement → strong solution: ż integrable on every [t₀,T], z(t) = z(t₀) + ∫_{t₀}^{t} ż for every t ≥ t₀, (6) for almost every t ≥ t₀ (IsPerturbedSDStrongSolution); reason: g is only assumed to satisfy (7), so a classical reading would exclude every discontinuous g; every classical solution (differentiable at every t ≥ t₀ with (6) there, g satisfying (7)) is a strong solution, since ż is then locally integrable and the fundamental theorem of calculus applies, so the statement specializes to the source under either reading
--   - encoding: z, g defined on [t₀,+∞[ → z, g : ℝ to H, constrained on Set.Ici t₀ only; reason: values before t₀ enter no hypothesis and no conclusion
--   - reading: the time origin t₀ > 0 fixed on p.2; the statement does not repeat it → hypothesis 0 < t₀; reason: a standing assumption of the paper, not repeated in the statement
--   - encoding: each "∫ … < +∞" → IntegrableOn of the printed integrand on Set.Ici; reason: the integrand is nonnegative and measurable, so the two conditions coincide
--   - encoding: inf_H f → the real infimum ⨅ y, f y; reason: S ≠ ∅ makes f bounded below, so the real infimum is the true one
--   - encoding: z(t) converges weakly and its limit belongs to S → ∃ p ∈ argminSet f, InertialAVD.Traj.WeakTendstoAtTop z p; reason: weak convergence is ⟨·,v⟩ convergence for every v, as written on p.8
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Theorem 1, p.3

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_IsPerturbedSDStrongSolution

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Theorem 1 (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.3). Suppose `f` satisfies (A), and let
`z` be a solution trajectory of (6), `ż(t) + ∇f(z(t)) = g(t)`, with
`∫_{t₀}^{+∞} ‖g(t)‖ dt < +∞` and `∫_{t₀}^{+∞} t ‖g(t)‖² dt < +∞` (7). Then
(i) `∫_{t₀}^{+∞} t ‖ż(t)‖² dt < +∞`;
(ii) `∫_{t₀}^{+∞} t ‖∇f(z(t))‖² dt < +∞`;
(iii) `∫_{t₀}^{+∞} (f(z(t)) - inf_H f) dt < +∞`;
(iv) `f(z(t)) - inf_H f = o(1/t)` as `t → +∞`;
(v) `z(t)` converges weakly as `t → +∞`, and its limit belongs to `S = argmin f`.
If `∫_{t₀}^{+∞} t² ‖g(t)‖² dt < +∞`, then
(vi) `‖∇f(z(t))‖ = o(1/t)` as `t → +∞`.

**Formalization Note.** "`∫ … < +∞`" is integrability on `[t₀, +∞[` of the printed integrand. The
real infimum `⨅ y, f y` is `inf_H f` because `S ≠ ∅` makes `f` bounded below. A solution is a strong
solution (`IsPerturbedSDStrongSolution`: `z` locally absolutely continuous with derivative `zdot`,
(6) for almost every `t ≥ t₀`), since `g` is only assumed to satisfy (7); every classical solution is
one. `0 < t₀` is the standing time origin of p.2. -/
theorem theorem_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {t₀ : ℝ} (ht₀ : 0 < t₀) {z zdot g : ℝ → H}
    (hz : IsPerturbedSDStrongSolution f g t₀ z zdot)
    (hg₁ : IntegrableOn (fun t => ‖g t‖) (Set.Ici t₀))
    (hg₂ : IntegrableOn (fun t => t * ‖g t‖ ^ 2) (Set.Ici t₀)) :
    IntegrableOn (fun t => t * ‖zdot t‖ ^ 2) (Set.Ici t₀) ∧
      IntegrableOn (fun t => t * ‖gradient f (z t)‖ ^ 2) (Set.Ici t₀) ∧
      IntegrableOn (fun t => f (z t) - ⨅ y, f y) (Set.Ici t₀) ∧
      (fun t => f (z t) - ⨅ y, f y) =o[atTop] (fun t : ℝ => 1 / t) ∧
      (∃ p ∈ argminSet f, InertialAVD.Traj.WeakTendstoAtTop z p) ∧
      (IntegrableOn (fun t => t ^ 2 * ‖g t‖ ^ 2) (Set.Ici t₀) →
        (fun t => ‖gradient f (z t)‖) =o[atTop] (fun t : ℝ => 1 / t)) := by sorry

end TimeScaleAvg
