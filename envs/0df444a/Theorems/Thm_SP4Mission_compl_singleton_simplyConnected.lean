-- Prove2me | Theorems.Thm_SP4Mission_compl_singleton_simplyConnected
-- name    : SP4Mission.compl_singleton_simplyConnected
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-09T01:54:19.190742+00:00
-- url     : https://prove2.me/theorems/15ac860c-dda2-476d-b7d7-781659d5fe51
-- title:
--   Removing a point from a simply connected $n$-manifold, $n\ge3$, leaves it simply connected
-- statement:
--   Let $n\ge3$ and let $M$ be a Hausdorff topological space with a charted-space structure modeled on $\mathbb R^n$ (a topological $n$-manifold without boundary), and assume $M$ is simply connected. Then for every point $p\in M$ the punctured manifold $M\setminus\{p\}$ is simply connected:
--
--   $$
--   \pi_1(M)=0,\ n\ge3\quad\Longrightarrow\quad \pi_1\bigl(M\setminus\{p\}\bigr)=0 .
--   $$
--
--   This is the standard consequence of van Kampen's theorem for the open cover of $M$ by $M\setminus\{p\}$ and a coordinate ball $B$ around $p$: the intersection $B\setminus\{p\}\simeq S^{n-1}$ is path connected and simply connected for $n\ge3$, so $\pi_1(M)$ is the free product of $\pi_1(M\setminus\{p\})$ and $\pi_1(B)=0$. The hypothesis $n\ge3$ is necessary: removing a point from $S^2$ leaves the plane, which is simply connected, but removing a point from the simply connected manifold $\mathbb R^2$ gives $\pi_1=\mathbb Z$. It supplies the fundamental-group input for the weak contractibility of a punctured homotopy four-sphere, where Freedman records that the punctured manifolds $M-\mathrm{pt}$ are $1$-connected.
--
--   **Formalization Note** Simple connectivity is Mathlib's `SimplyConnectedSpace` (path connected with trivial fundamental groupoid). No compactness or second countability is assumed; the manifold hypothesis is a topological atlas `ChartedSpace (EuclideanSpace ℝ (Fin n)) M`.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Theorem 1.20 (van Kampen's theorem), p. 43, applied to the cover by M − {p} and a coordinate ball, with Proposition 1.14, p. 35 (π₁(Sⁿ) = 0 for n ≥ 2) for the intersection; the Euclidean case is §1.2, Exercise 3, p. 53 ("the complement of a finite set of points in Rⁿ is simply-connected if n ≥ 3"). Use in the source: Michael H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357–453, https://doi.org/10.4310/jdg/1214437136, proof of Theorem 1.5, p. 369: "(W; M′ − pt, M − pt) is a (topological) proper h-cobordism which is 1-connected". Reduction child of SP4Mission.punctured_homotopy_sphere_weaklyContractible.

import Definitions.Def_SP4Sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.compl_singleton_simplyConnected
    (n : ℕ) (hn : 3 ≤ n) (M : Type*) [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) :
    SimplyConnectedSpace {x : M // x ≠ p} := by sorry
