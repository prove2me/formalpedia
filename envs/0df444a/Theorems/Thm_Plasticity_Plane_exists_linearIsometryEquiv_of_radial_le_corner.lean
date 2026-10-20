-- Prove2me | Theorems.Thm_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le_corner
-- name    : Plasticity.Plane.exists_linearIsometryEquiv_of_radial_le_corner
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:28.070152+00:00
-- url     : https://prove2.me/theorems/3cb4aa03-1f84-40c6-82ff-022d5d5c84e7
-- title:
--   Two adjacent edges in the target ball: a map of extreme points of planar balls satisfying the radial inequality is inverted by a linear isometry
-- statement:
--   Let $V,W$ be real normed spaces of dimension $2$ with closed unit balls $D_V,D_W$, and let $g\colon W\to V$ map the extreme points of $D_W$ to extreme points of $D_V$ and satisfy the radial inequality $$\|\alpha w+\beta w'\|\le\|\alpha g(w)+\beta g(w')\|\qquad(w,w'\in\operatorname{ext}D_W,\ \alpha,\beta\in\mathbb R).$$
--   Suppose $D_W$ has pairwise distinct extreme points $a,b,c$ with $\|a+b\|=\|b+c\|=2$, that is, two edges $[a,b]$ and $[b,c]$ meeting at $b$.
--   Then there is a surjective linear isometry $L\colon V\to W$ with $L(g(w))=w$ for every extreme point $w$ of $D_W$.
--   The map $g$ is not assumed odd, and its values off $\operatorname{ext}D_W$ do not matter.
-- source:
--   This repository: claims CUB106(3) and CUB108 (claims/cub.md), expositions/c0_planar_mixtures.md §§2, 4, in a form that needs only one corner of the target ball

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.Plane
theorem exists_linearIsometryEquiv_of_radial_le_corner {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hV : Module.finrank ℝ V = 2) (hW : Module.finrank ℝ W = 2) (g : W → V)
    (hext : Set.MapsTo g (Set.extremePoints ℝ (Metric.closedBall (0 : W) 1))
      (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)))
    (hrad : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
      ∀ w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖)
    {a b c : W} (ha : a ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1))
    (hb : b ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1))
    (hc : c ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1))
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hab2 : ‖a + b‖ = 2) (hbc2 : ‖b + c‖ = 2) :
    ∃ L : V ≃ₗᵢ[ℝ] W, ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), L (g w) = w := by
  sorry
end Plasticity.Plane
