-- Prove2me | Theorems.Thm_Plasticity_Plane_exists_linearIsometryEquiv_of_contraction_of_extremePoints
-- name    : Plasticity.Plane.exists_linearIsometryEquiv_of_contraction_of_extremePoints
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:29.565323+00:00
-- url     : https://prove2.me/theorems/82f4fe18-1533-43a2-914e-b48cdb190c89
-- title:
--   A linear contraction between spaces of equal finite dimension whose image of the ball contains every extreme point of the target ball is an onto isometry
-- statement:
--   Let $V,W$ be finite-dimensional real normed spaces of the same dimension, let $A\colon V\to W$ be linear with $\|Av\|\le\|v\|$ for every $v\in V$, and let $g\colon W\to V$ satisfy $$\|g(w)\|\le1\quad\text{and}\quad A(g(w))=w$$ for every extreme point $w$ of the closed unit ball of $W$.
--   Then $A$ is a linear isometry of $V$ onto $W$: there is a surjective linear isometry $L\colon V\to W$ with $Lv=Av$ for every $v\in V$.
--   Only the values of $g$ at extreme points enter; the hypothesis says that the image under $A$ of the closed unit ball of $V$ contains every extreme point of the closed unit ball of $W$.
-- source:
--   This repository: closing step of claim CUB101 (claims/cub.md), Proposition 3.2 in expositions/c0_separated_edge_planes.md §3, also used for claims CUB106(3) and CUB108 (expositions/c0_planar_mixtures.md §§2, 4); with the Krein–Milman theorem

import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.Plane
theorem exists_linearIsometryEquiv_of_contraction_of_extremePoints {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W)
    (A : V →ₗ[ℝ] W) (hA : ∀ v, ‖A v‖ ≤ ‖v‖) (g : W → V)
    (hg : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
      ‖g w‖ ≤ 1 ∧ A (g w) = w) :
    ∃ L : V ≃ₗᵢ[ℝ] W, ∀ v, L v = A v := by sorry
end Plasticity.Plane
