-- Prove2me | Theorems.Thm_Plasticity_Plane_exists_corner_of_bad
-- name    : Plasticity.Plane.exists_corner_of_bad
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-19T19:01:28.747403+00:00
-- url     : https://prove2.me/theorems/8a61af07-f653-4777-b037-33ce29816b32
-- title:
--   A bad direction of a non-parallelogram plane lies near a corner where two edges meet
-- statement:
--   Let $V$ be a real normed space of dimension $2$ whose closed unit ball $D$ has more than four extreme points.
--   Let $e\in V$ with $\|e\|=1$ be *bad*: at most one extreme point $p$ of $D$ has $\|p-e\|<1$.
--   Then there are extreme points $x,x_1,x_2$ of $D$ and functionals $f_1,f_2$ of norm $1$ with $$\|x-e\|<1,\quad x_1\ne x,\quad x_2\ne x,\quad f_1(x_1)=f_1(x)=1,\quad f_2(x)=f_2(x_2)=1,\quad f_1(x_2)<1,\quad f_2(x_1)<1,\quad \|x_2-x\|<2.$$
--   So $x$ is the only extreme point within distance less than one of $e$, and the edges $[x_1,x]$ and $[x,x_2]$ of $D$ meet at $x$; these are the hypotheses of the card `Plasticity.Plane.corner_cover`.
-- source:
--   This repository: claim CUB102(2) (claims/cub.md), proof in expositions/c0_planes_front.md §2.2

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Plasticity.Plane
theorem exists_corner_of_bad {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hV : Module.finrank ℝ V = 2)
    (hpar : 4 < (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)).encard)
    (e : V) (he : ‖e‖ = 1)
    (hbad : ∀ p ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
      ∀ q ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖p - e‖ < 1 → ‖q - e‖ < 1 → p = q) :
    ∃ x ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1), ‖x - e‖ < 1 ∧
      ∃ x₁ ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
      ∃ x₂ ∈ Set.extremePoints ℝ (Metric.closedBall (0 : V) 1),
      ∃ f₁ f₂ : StrongDual ℝ V, ‖f₁‖ = 1 ∧ ‖f₂‖ = 1 ∧ x₁ ≠ x ∧ x₂ ≠ x ∧
        f₁ x₁ = 1 ∧ f₁ x = 1 ∧ f₂ x = 1 ∧ f₂ x₂ = 1 ∧ f₁ x₂ < 1 ∧ f₂ x₁ < 1 ∧
        ‖x₂ - x‖ < 2 := by sorry
end Plasticity.Plane
