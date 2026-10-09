-- Prove2me | Theorems.Thm_RayBundle_GraphRealization_vertex_dist
-- name    : RayBundle.GraphRealization.vertex_dist
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-10-08T18:56:56.320101+00:00
-- url     : https://prove2.me/theorems/26ddbfbf-c99b-4e39-a640-9ecf40c73bc2
-- title:
--   Vertex distances in the unit-edge realization equal graph distances
-- statement:
--   Let $T$ be a connected simple graph on a vertex type $V$, with an explicit edge enumeration $e:\mathbb N\simeq E(T)$; in particular its edge set is countably infinite. Let $|T|_e$ be the unit-edge metric realization formed by successive isometric interval attachments and their metric inductive limit. Write $\iota:V\to|T|_e$ for its vertex map and $\epsilon_n:[0,1]\to|T|_e$ for its $n$th edge map.
--
--   For all vertices $v,w$, $$d(\iota(v),\iota(w))=d_T(v,w).$$ The combinatorial distance on the right is interpreted as a real number.
-- source:
--   Standard unit-edge metric-graph convention: Nicholas Touikan, On geodesic ray bundles in hyperbolic groups, Proceedings of the American Mathematical Society 146 (2018), 4165–4173, Section 2. https://arxiv.org/abs/1706.01979 The present construction and supporting lemmas are proved in the supplied Lean development; these targets are not assigned numbered theorem attributions in that paper.

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry

universe u

theorem RayBundle.GraphRealization.vertex_dist {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (v w : V) :
    dist (RayBundle.GraphRealization.vertex T hT e v) (RayBundle.GraphRealization.vertex T hT e w) = (T.dist v w : ℝ) := by sorry
