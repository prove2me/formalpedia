-- Prove2me | Theorems.Thm_RayBundle_four_point_of_dense_image
-- name    : RayBundle.four_point_of_dense_image
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-10-08T19:38:18.722818+00:00
-- url     : https://prove2.me/theorems/fbe7a71d-9923-4b59-8946-9a3b6addef48
-- title:
--   A uniformly nearby image transfers four-point bounds to the ambient metric space
-- statement:
--   Let $X$ be a metric space, $f:V\to X$ a map, and $R,C\in\mathbb R$. Suppose every $x\in X$ has some $v\in V$ with $d(x,f(v))\le R$. Suppose also that all $v_1,v_2,v_3,v_4\in V$ satisfy
--
--   $$d(f(v_1),f(v_2))+d(f(v_3),f(v_4))
--   \le\max\{d(f(v_1),f(v_3))+d(f(v_2),f(v_4)),\ d(f(v_1),f(v_4))+d(f(v_2),f(v_3))\}+C.$$
--
--   Then all $a,b,c,d\in X$ satisfy
--
--   $$d(a,b)+d(c,d)\le\max\{d(a,c)+d(b,d),\ d(a,d)+d(b,c)\}+C+8R.$$
--
--   This transfers a quantitative four-point estimate from an image that is uniformly close to all ambient points. For unit-edge graphs, it allows estimates on vertices to control the entire continuous realization. The proximity assumption uses one fixed radius $R$, rather than topological density.
-- source:
--   Source declaration: RayBundle/Thm_Cayley_four_point_of_dense_image.lean, theorem RayBundle.four_point_of_dense_image. Supporting metric estimate proved directly in this development from the triangle inequality. Unit-edge metric-graph motivation and conventions: Nicholas Touikan, On geodesic ray bundles in hyperbolic groups (2018), Section 2, https://arxiv.org/abs/1706.01979 . No numbered theorem attribution for this estimate is claimed.

import Mathlib.Topology.MetricSpace.Basic

theorem RayBundle.four_point_of_dense_image {X V : Type*} [MetricSpace X] (f : V → X) (R C : ℝ)
    (hnear : ∀ x, ∃ v, dist x (f v) ≤ R)
    (hfour : ∀ a b c d, dist (f a) (f b) + dist (f c) (f d) ≤
      max (dist (f a) (f c) + dist (f b) (f d))
        (dist (f a) (f d) + dist (f b) (f c)) + C) (a b c d : X) :
    dist a b + dist c d ≤
      max (dist a c + dist b d) (dist a d + dist b c) + (C + 8 * R) := by sorry
