-- Prove2me | Theorems.Thm_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le_uncountable
-- name    : Plasticity.Plane.exists_linearIsometryEquiv_of_radial_le_uncountable
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:28.360102+00:00
-- url     : https://prove2.me/theorems/42288b69-c993-4443-971c-70876828075d
-- title:
--   Uncountably many extreme points in the target ball: a map satisfying the radial inequality is inverted by a linear isometry of planes
-- statement:
--   Let $V,W$ be real normed spaces of dimension $2$ with closed unit balls $D_V,D_W$, where $D_W$ has uncountably many extreme points.
--   Let $g\colon W\to V$ satisfy $\|g(w)\|\le1$ for every extreme point $w$ of $D_W$ and the radial inequality $$\|\alpha w+\beta w'\|\le\|\alpha g(w)+\beta g(w')\|\qquad(w,w'\in\operatorname{ext}D_W,\ \alpha,\beta\in\mathbb R).$$
--   Then there is a surjective linear isometry $L\colon V\to W$ with $L(g(w))=w$ for every extreme point $w$ of $D_W$.
--   The map $g$ is assumed neither to send extreme points to extreme points nor to be odd.
-- source:
--   This repository: claim CUB101 (claims/cub.md), Proposition 3.2 in expositions/c0_separated_edge_planes.md §3, here without derivatives and without oddness of g

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.Plane
theorem exists_linearIsometryEquiv_of_radial_le_uncountable {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hV : Module.finrank ℝ V = 2) (hW : Module.finrank ℝ W = 2) (g : W → V)
    (hball : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), ‖g w‖ ≤ 1)
    (hrad : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
      ∀ w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    (hunc : ¬ (Set.extremePoints ℝ (Metric.closedBall (0 : W) 1)).Countable) :
    ∃ L : V ≃ₗᵢ[ℝ] W, ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), L (g w) = w := by
  sorry
end Plasticity.Plane
