-- Prove2me | Theorems.Thm_RayBundle_MetricSegment_four_point_thin
-- name    : RayBundle.MetricSegment.four_point_thin
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-10-08T19:38:24.000841+00:00
-- url     : https://prove2.me/theorems/06ba40c9-f9d1-47ec-ab70-b0c15fee7c66
-- title:
--   Four-point error K implies 2K-thinness of geodesic triangles
-- statement:
--   Let $X$ be a metric space and $K\ge0$. Suppose all $x,y,z,w\in X$ satisfy
--
--   $$d(x,y)+d(z,w)\le\max\{d(x,z)+d(y,w),\ d(x,w)+d(y,z)\}+K.$$
--
--   Let $[a,b]$, $[a,c]$, and $[b,c]$ be specified arc-length geodesic segments. Every point $p$ on $[a,b]$ has a point $q$ on one of the other two segments with
--
--   $$q\in[a,c]\cup[b,c],\qquad d(p,q)\le2K.$$
--
--   Applying the result to each side gives a $2K$-thin geodesic triangle. The theorem concerns any three supplied segments; it does not assume global geodesic existence. With the four-point convention whose error is $2\delta$, this estimate gives $4\delta$-thinness.
-- source:
--   Source declaration: RayBundle/Thm_Cayley_MetricSegment_four_point_thin.lean, theorem RayBundle.MetricSegment.four_point_thin. Supporting quantitative hyperbolicity lemma proved in this development using two four-point comparisons. Thin-triangle and unit-edge graph conventions are described in Nicholas Touikan, On geodesic ray bundles in hyperbolic groups (2018), Section 2, https://arxiv.org/abs/1706.01979 . The constant here is the explicitly proved bound, not a numbered theorem attribution in that paper.

import Definitions.Def_RayBundle_MetricPathGeometry

theorem RayBundle.MetricSegment.four_point_thin {X : Type*} [MetricSpace X] (K : ℝ) (hK : 0 ≤ K)
    (hfour : ∀ a b c d : X, dist a b + dist c d ≤
      max (dist a c + dist b d) (dist a d + dist b c) + K)
    {a b c : X} (ab : RayBundle.MetricSegment a b) (ac : RayBundle.MetricSegment a c) (bc : RayBundle.MetricSegment b c)
    (t : Set.Icc (0 : ℝ) (dist a b)) :
    ∃ q, (q ∈ Set.range ac.map ∨ q ∈ Set.range bc.map) ∧ dist (ab.map t) q ≤ 2 * K := by sorry
