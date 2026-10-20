-- Prove2me | Theorems.Thm_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le
-- name    : Plasticity.Plane.exists_linearIsometryEquiv_of_radial_le
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:28.083567+00:00
-- url     : https://prove2.me/theorems/7d6b02b7-fe22-4c7a-a9ff-85bbd5a3932f
-- title:
--   Linearization of the extreme correspondence: a map of extreme points of planar balls satisfying the radial inequality is inverted by a linear isometry
-- statement:
--   Let $V,W$ be real normed spaces of dimension $2$ with closed unit balls $D_V,D_W$, and let $g\colon W\to V$ map the extreme points of $D_W$ to extreme points of $D_V$ and satisfy the radial inequality $$\|\alpha w+\beta w'\|\le\|\alpha g(w)+\beta g(w')\|\qquad(w,w'\in\operatorname{ext}D_W,\ \alpha,\beta\in\mathbb R).$$
--   Then there is a surjective linear isometry $L\colon V\to W$ with $L(g(w))=w$ for every extreme point $w$ of $D_W$.
--   The map $g$ is not assumed odd, and no condition on the shapes of $D_V$ and $D_W$ is imposed.
-- source:
--   This repository: claims CUB101 (Proposition 3.2, expositions/c0_separated_edge_planes.md §3), CUB106(3) and CUB108 (claims/cub.md; expositions/c0_planar_mixtures.md §§2, 4), which linearize the extreme correspondence of a block pair; here the cases are only a countable and an uncountable extreme set of the target ball

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.Plane
theorem exists_linearIsometryEquiv_of_radial_le {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hV : Module.finrank ℝ V = 2) (hW : Module.finrank ℝ W = 2) (g : W → V)
    (hext : Set.MapsTo g (Set.extremePoints ℝ (Metric.closedBall (0 : W) 1))
      (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)))
    (hrad : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
      ∀ w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖) :
    ∃ L : V ≃ₗᵢ[ℝ] W, ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), L (g w) = w := by
  sorry
end Plasticity.Plane
