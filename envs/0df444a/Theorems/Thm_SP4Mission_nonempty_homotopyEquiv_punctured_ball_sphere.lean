-- Prove2me | Theorems.Thm_SP4Mission_nonempty_homotopyEquiv_punctured_ball_sphere
-- name    : SP4Mission.nonempty_homotopyEquiv_punctured_ball_sphere
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-08T05:32:36.238318+00:00
-- url     : https://prove2.me/theorems/bd243d1a-92e6-476d-8c2e-b96006de3189
-- title:
--   A punctured open ball in a real normed space is homotopy equivalent to the unit sphere
-- statement:
--   Let $E$ be a real normed vector space, let $c\in E$ and let $r>0$. The punctured open ball $B(c,r)\setminus\{c\}$, with the subspace topology, is homotopy equivalent to the unit sphere $S(E)=\{u\in E:\|u\|=1\}$:
--
--   $$
--   B(c,r)\setminus\{c\}\;\simeq\;S(E).
--   $$
--
--   A homotopy equivalence is given by radial projection $y\mapsto (y-c)/\|y-c\|$, with homotopy inverse the inclusion $u\mapsto c+\tfrac r2\,u$ of the sphere of radius $r/2$ about $c$; the composite on the punctured ball is homotopic to the identity through the radial deformation $y\mapsto c+\bigl((1-t)\tfrac r2+t\|y-c\|\bigr)\,\frac{y-c}{\|y-c\|}$, $t\in[0,1]$, which stays in the punctured ball. This is the deformation retraction of $\mathbb R^n\setminus\{0\}$ onto $S^{n-1}$ (Hatcher, Chapter 0, Exercise 2), restricted to a ball and stated for an arbitrary real normed space. Its role here is to transport simple connectivity from the sphere to punctured coordinate balls in a manifold: a punctured coordinate ball in an $n$-manifold, $n\ge3$, is simply connected because $S^{n-1}$ is.
--
--   **Formalization Note** The statement is `Nonempty (ContinuousMap.HomotopyEquiv ↥(Metric.ball c r \ {c}) ↥(Metric.sphere (0 : E) 1))`, Mathlib's notion of homotopy equivalence between the two subtypes. No finite-dimensionality or inner-product structure is assumed on `E`.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Chapter 0, Exercises, Exercise 2, p. 18: "Construct an explicit deformation retraction of Rⁿ − {0} onto S^{n−1}"; here the radial deformation is restricted to the open ball B(c, r) about c, retracting onto the sphere of radius r/2, in an arbitrary real normed space. Reduction child of SP4Mission.compl_singleton_simplyConnectedAtInfinity.

import Definitions.Def_SP4Sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission

theorem SP4Mission.nonempty_homotopyEquiv_punctured_ball_sphere
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) {r : ℝ} (hr : 0 < r) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(Metric.ball c r \ {c}) ↥(Metric.sphere (0 : E) 1)) := by
  sorry
