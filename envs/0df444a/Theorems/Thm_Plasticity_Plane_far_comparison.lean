-- Prove2me | Theorems.Thm_Plasticity_Plane_far_comparison
-- name    : Plasticity.Plane.far_comparison
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:27.408385+00:00
-- url     : https://prove2.me/theorems/e2d70c6f-1c93-45e4-bd04-832f928ab68f
-- title:
--   Far comparison: a small move of $tu$ that approaches no far extreme point stays within $1-t$ of the extreme point $u$
-- statement:
--   Let $V$ be a real normed space of dimension $2$ with closed unit ball $D$, let $u$ be an extreme point of $D$, and let $0<t<1$.
--   There is $\rho>0$ such that every $h\in V$ with $\|h\|<\rho$ and $$\|tu-\omega\|\le\|tu+h-\omega\|\quad\text{for every extreme point }\omega\text{ of }D\text{ with }\|tu-\omega\|>1$$ satisfies $$\|(1-t)u-h\|\le1-t,$$ that is, $\|u-(tu+h)\|\le1-t$.
-- source:
--   This repository: claim CUB99(4) (claims/cub.md), proof in expositions/c0_one_general_plane.md §2.5

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.Plane
theorem far_comparison {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2) (u : V)
    (hu : u ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ ρ > 0, ∀ h : V, ‖h‖ < ρ →
      (∀ ω ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), 1 < ‖t • u - ω‖ →
        ‖t • u - ω‖ ≤ ‖t • u + h - ω‖) →
      ‖(1 - t) • u - h‖ ≤ 1 - t := by sorry
end Plasticity.Plane
