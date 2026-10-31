-- Prove2me | Theorems.Thm_TimeScaleAvg_eq_41_42
-- name    : TimeScaleAvg.eq_41_42
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:15.870163+00:00
-- url     : https://prove2.me/theorems/cd2bd302-eba3-4414-a31b-365291e2ea84
-- title:
--   Eqs. (41)–(42) — estimates for the unperturbed steepest descent
-- statement:
--   Let $f$ satisfy $(\mathcal A)$. For any solution $z$ on $[t_0,+\infty[$ of (SD), $\dot z(t)+\nabla f(z(t))=0$,
--
--   $$
--   \int_{t_0}^{+\infty}t\|\dot z(t)\|^2\,dt<+\infty,\qquad\int_{t_0}^{+\infty}t\|\nabla f(z(t))\|^2\,dt<+\infty,
--   $$
--
--   and $\|\nabla f(z(t))\|=o(1/t)$, $\|\dot z(t)\|=o(1/t)$ as $t\to+\infty$.
--
--   This is the case $g\equiv0$ of Theorem 1, in the form used in the proof of Theorem 2.
--
--   Differences from the source:
--   - reading: z : [t₀,+∞[ to H a solution trajectory of (6), the notion not spelled out in the statement → maps z, ż : ℝ to H with ż the derivative of z within [t₀,+∞[ at every t ≥ t₀ (one-sided at t₀), with (6) at every t ≥ t₀; continuity of ż and of g is not required; reason: p.2 calls the solution classical and the proof differentiates at every t; a C¹ solution is a special case, so the source result is covered
--   - encoding: z, g defined on [t₀,+∞[ → z, g : ℝ to H, constrained on Set.Ici t₀ only; reason: values before t₀ enter no hypothesis and no conclusion
--   - reading: the time origin t₀ > 0 fixed on p.2; the statement does not repeat it → hypothesis 0 < t₀; reason: a standing assumption of the paper, not repeated in the statement
--   - encoding: each "∫ … < +∞" → IntegrableOn of the printed integrand on Set.Ici; reason: the integrand is nonnegative and measurable, so the two conditions coincide
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eqs. (40)–(42), p.7

import Mathlib
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_IsPerturbedSDSolution

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Eqs. (41)–(42) (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.7). For any solution trajectory of
(SD), `ż(t) + ∇f(z(t)) = 0`: `∫_{t₀}^{+∞} t ‖ż(t)‖² dt < +∞`, `∫_{t₀}^{+∞} t ‖∇f(z(t))‖² dt < +∞`,
`‖∇f(z(t))‖ = o(1/t)` and `‖ż(t)‖ = o(1/t)` as `t → +∞`.

**Formalization Note.** (SD) is (6) with `g ≡ 0`. -/
theorem eq_41_42 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {t₀ : ℝ} (ht₀ : 0 < t₀) {z zdot : ℝ → H}
    (hz : IsPerturbedSDSolution f (fun _ => 0) t₀ z zdot) :
    IntegrableOn (fun t => t * ‖zdot t‖ ^ 2) (Set.Ici t₀) ∧
      IntegrableOn (fun t => t * ‖gradient f (z t)‖ ^ 2) (Set.Ici t₀) ∧
      (fun t => ‖gradient f (z t)‖) =o[atTop] (fun t : ℝ => 1 / t) ∧
      (fun t => ‖zdot t‖) =o[atTop] (fun t : ℝ => 1 / t) := by sorry

end TimeScaleAvg
