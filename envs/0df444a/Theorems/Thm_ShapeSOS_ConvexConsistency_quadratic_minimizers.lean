-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_quadratic_minimizers
-- name    : ShapeSOS.ConvexConsistency.quadratic_minimizers
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:22:05.941205+00:00
-- url     : https://prove2.me/theorems/c50d5bc2-c31a-491e-8edc-26ed52838b27
-- title:
--   Theorem B.8 — objective convergence implies convergence to the quadratic minimizer
-- statement:
--   Let $q:\mathbb R^n\to\mathbb R$ be a strictly convex quadratic function, written as $q(x)=x^TAx+b^Tx+c$. Let $S$ be a closed convex set and let $x^*\in S$ minimize $q$ over $S$. This minimizer is unique by strict convexity. For every sequence $x_j\in S$ satisfying $q(x_j)\to q(x^*)$,
--   $$\|x_j-x^*\|_2\longrightarrow0.$$
--   The sequence is not assumed convergent. The premise that $x^*$ is an attained minimizer already makes $S$ nonempty; existence or uniqueness is not replaced by an assumption of convergence.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
--   - encoding: named minimizers of the displayed problems → concrete feasible sets, losses, and attained-minimum relations; reason: optimality compares against every feasible polynomial; it is never replaced by a desired asymptotic property
--   - encoding: a strictly convex quadratic function → the complete coordinate formula xᵀAx+bᵀx+c with StrictConvexOn on all of real space; reason: every real quadratic has this representation; symmetry of A is unnecessary because its antisymmetric part contributes zero
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 31, Theorem B.8

import Definitions.Def_ShapeSOS_ConvexConsistency_Geometry

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem quadratic_minimizers (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Vec n) (c : ℝ) (hstrict : StrictConvexOn ℝ Set.univ (quadratic A b c))
    (S : Set (Vec n)) (hclosed : IsClosed S) (hconvex : Convex ℝ S)
    (xstar : Vec n) (hmin : Minimizes S (quadratic A b c) xstar)
    (x : ℕ → Vec n) (hx : ∀ j, x j ∈ S)
    (hvalues : Tendsto (fun j => quadratic A b c (x j)) atTop (𝓝 (quadratic A b c xstar))) :
    Tendsto (fun j => norm₂ (x j - xstar)) atTop (𝓝 0) := by sorry

end ShapeSOS.ConvexConsistency
