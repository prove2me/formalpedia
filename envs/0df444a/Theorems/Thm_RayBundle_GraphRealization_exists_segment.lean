-- Prove2me | Theorems.Thm_RayBundle_GraphRealization_exists_segment
-- name    : RayBundle.GraphRealization.exists_segment
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-10-08T18:56:59.715584+00:00
-- url     : https://prove2.me/theorems/fde8dfea-fc80-454c-900c-a819775b4917
-- title:
--   The connected unit-edge graph realization is a geodesic metric space
-- statement:
--   Let $T$ be a connected simple graph on a vertex type $V$, with an explicit edge enumeration $e:\mathbb N\simeq E(T)$; in particular its edge set is countably infinite. Let $|T|_e$ be the unit-edge metric realization formed by successive isometric interval attachments and their metric inductive limit. Write $\iota:V\to|T|_e$ for its vertex map and $\epsilon_n:[0,1]\to|T|_e$ for its $n$th edge map.
--
--   For any $p,q\in|T|_e$, there is an isometry $c:[0,d(p,q)]\to|T|_e$ with $c(0)=p$ and $c(d(p,q))=q$. This includes endpoints in edge interiors and the case $p=q$.
-- source:
--   Standard unit-edge metric-graph convention: Nicholas Touikan, On geodesic ray bundles in hyperbolic groups, Proceedings of the American Mathematical Society 146 (2018), 4165–4173, Section 2. https://arxiv.org/abs/1706.01979 The present construction and supporting lemmas are proved in the supplied Lean development; these targets are not assigned numbered theorem attributions in that paper.

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry

universe u

theorem RayBundle.GraphRealization.exists_segment {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (p q : RayBundle.GraphRealization T hT e) :
    Nonempty (RayBundle.MetricSegment p q) := by sorry
