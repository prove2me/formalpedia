-- Prove2me | Theorems.Thm_RayBundle_intrinsicEDist_eq_of_segment
-- name    : RayBundle.intrinsicEDist_eq_of_segment
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-10-08T19:38:24.189587+00:00
-- url     : https://prove2.me/theorems/431ce83c-e895-450b-821d-4c6060c774b2
-- title:
--   A geodesic segment makes intrinsic path distance equal metric distance
-- statement:
--   Let $X$ be a metric space and let $a,b\in X$. Suppose there is an arc-length geodesic segment from $a$ to $b$: an isometry $c:[0,d(a,b)]\to X$ with the specified endpoints. Define intrinsic extended distance as the infimum of metric total variations of all continuous paths on $[0,1]$ joining the endpoints. Then
--
--   $$d_{\mathrm{intr}}(a,b)=d(a,b).$$
--
--   This applies to a single pair of endpoints whenever such a segment exists. In particular, every geodesic metric space has its intrinsic continuous-path metric. It includes the case $a=b$.
-- source:
--   Source declaration: RayBundle/Thm_Cayley_intrinsicEDist_eq_of_segment.lean, theorem RayBundle.intrinsicEDist_eq_of_segment. General metric lemma extracted from the already published proof infrastructure of the unit-edge graph realization: https://prove2.me/theorems/6283abac-8aeb-4ef6-bf5c-837bdc01f27b .

import Definitions.Def_RayBundle_MetricPathGeometry

theorem RayBundle.intrinsicEDist_eq_of_segment {X : Type*} [MetricSpace X] {a b : X}
    (c : RayBundle.MetricSegment a b) : RayBundle.intrinsicEDist a b = edist a b := by sorry
