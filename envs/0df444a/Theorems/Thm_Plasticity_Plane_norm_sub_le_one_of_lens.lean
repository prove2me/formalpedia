-- Prove2me | Theorems.Thm_Plasticity_Plane_norm_sub_le_one_of_lens
-- name    : Plasticity.Plane.norm_sub_le_one_of_lens
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:28.196111+00:00
-- url     : https://prove2.me/theorems/9c5624b9-6071-4af5-98ec-5195b3cc4b87
-- title:
--   The extreme lens: a point of a planar ball on which every functional norming an extreme point near $b$ is nonnegative lies within one of $b$
-- statement:
--   Let $V$ be a real normed space of dimension $2$ with closed unit ball $D$, and let $b,z\in D$.
--   Suppose that $f(z)\ge0$ for every extreme point $w$ of $D$ with $\|b-w\|\le1$ and every functional $f$ of norm $1$ with $f(w)=1$.
--   Then $$\|z-b\|\le1.$$
--   In the notation of claim CUB99(3), $D\cap C(b)\subseteq b+D$; neither $b\ne0$ nor $\|z\|=1$ is assumed.
-- source:
--   This repository: claim CUB99(3) (claims/cub.md), proof in expositions/c0_one_general_plane.md §2.4

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.Plane
theorem norm_sub_le_one_of_lens {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (b z : V) (hb : ‖b‖ ≤ 1) (hz : ‖z‖ ≤ 1)
    (hlens : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖b - w‖ ≤ 1 →
      ∀ f : StrongDual ℝ V, ‖f‖ = 1 → f w = 1 → 0 ≤ f z) :
    ‖z - b‖ ≤ 1 := by sorry
end Plasticity.Plane
