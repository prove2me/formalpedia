-- Prove2me | Theorems.Thm_SP4Mission_sphere_simplyConnected
-- name    : SP4Mission.sphere_simplyConnected
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T05:32:27.107274+00:00
-- url     : https://prove2.me/theorems/91945851-6894-43f5-a6d9-2bff24c3e43d
-- title:
--   $\pi_1(S^{n-1}) = 0$ for $n \ge 3$: the unit sphere in $\mathbb R^n$ is simply connected
-- statement:
--   Let $n\ge3$ and let $S^{n-1}=\{x\in\mathbb R^n:\|x\|=1\}$ be the unit sphere of Euclidean $n$-space, with the subspace topology. Then $S^{n-1}$ is simply connected: it is path connected and every loop in it is null-homotopic, i.e.
--
--   $$
--   \pi_1(S^{n-1},x_0)=0\qquad\text{for every base point } x_0\in S^{n-1}.
--   $$
--
--   In the usual indexing this is $\pi_1(S^m)=0$ for $m\ge2$ (Hatcher, Proposition 1.14), where $S^m\subset\mathbb R^{m+1}$; here $m=n-1\ge2$. It is the basic input showing that punctured Euclidean balls and punctured Euclidean spaces of dimension at least three are simply connected, and hence that the complement of a point in a compact manifold of dimension at least three is simply connected at infinity. The statement is false for $n=2$, where $S^1$ has fundamental group $\mathbb Z$, and for $n=1$, where $S^0$ is not connected.
--
--   **Formalization Note** `SimplyConnectedSpace` is Mathlib's notion: the fundamental groupoid is equivalent to the trivial groupoid, equivalently the space is path connected and any two paths with the same end points are homotopic (`SimplyConnectedSpace.paths_homotopic`). The sphere is the subtype `Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1`, so for `n = 5` it is exactly the mission's `S4`.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Section 1.1, Proposition 1.14, p. 35: "π₁(Sⁿ) = 0 if n ≥ 2", stated here for the unit sphere of Rⁿ with n ≥ 3 (so the sphere is S^{n-1} with n − 1 ≥ 2). Used, via the punctured coordinate ball, in SP4Mission.compl_singleton_simplyConnectedAtInfinity (Freedman 1982, p. 369 and p. 436). Reduction child of SP4Mission.compl_singleton_simplyConnectedAtInfinity.

import Definitions.Def_SP4Sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.sphere_simplyConnected (n : ℕ) (hn : 3 ≤ n) :
    SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by sorry
