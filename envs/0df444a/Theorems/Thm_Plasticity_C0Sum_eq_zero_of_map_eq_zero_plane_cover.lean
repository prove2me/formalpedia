-- Prove2me | Theorems.Thm_Plasticity_C0Sum_eq_zero_of_map_eq_zero_plane_cover
-- name    : Plasticity.C0Sum.eq_zero_of_map_eq_zero.plane_cover
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:26.790262+00:00
-- url     : https://prove2.me/theorems/15fda856-a340-42db-a69b-d79be560fe70
-- title:
--   In a plane whose ball has more than four extreme points, every nonzero point of the ball is within distance less than one of an extreme point
-- statement:
--   Let $V$ be a real normed space of dimension $2$ whose closed unit ball $D$ has more than four extreme points.
--   Then every $b\in D$ with $b\ne0$ satisfies $\|b-e\|<1$ for some extreme point $e$ of $D$.
-- source:
--   This repository: claim CUB100 (claims/cub.md), Lemma 2.1(3) in expositions/c0_one_general_plane.md §2.1

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.C0Sum.eq_zero_of_map_eq_zero
theorem plane_cover {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2)
    (h4 : 4 < (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)).encard)
    (b : V) (hb : ‖b‖ ≤ 1) (hb0 : b ≠ 0) :
    ∃ e ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖b - e‖ < 1 := by sorry
end Plasticity.C0Sum.eq_zero_of_map_eq_zero
