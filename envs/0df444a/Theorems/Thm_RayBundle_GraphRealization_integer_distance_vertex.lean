-- Prove2me | Theorems.Thm_RayBundle_GraphRealization_integer_distance_vertex
-- name    : RayBundle.GraphRealization.integer_distance_vertex
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-10-08T18:57:01.03387+00:00
-- url     : https://prove2.me/theorems/c443a13a-8147-4e92-8bd1-abfd2cc301da
-- title:
--   Integer-distance spheres about graph vertices contain only vertices
-- statement:
--   Let $T$ be a connected simple graph on a vertex type $V$, with an explicit edge enumeration $e:\mathbb N\simeq E(T)$; in particular its edge set is countably infinite. Let $|T|_e$ be the unit-edge metric realization formed by successive isometric interval attachments and their metric inductive limit. Write $\iota:V\to|T|_e$ for its vertex map and $\epsilon_n:[0,1]\to|T|_e$ for its $n$th edge map.
--
--   If $v\in V$, $n\in\mathbb N$, and $p\in|T|_e$ satisfies $d(p,\iota(v))=n$, then $p=\iota(w)$ for some vertex $w$. This is the vertex-detection fact used when sampling a continuous geodesic ray at integer times.
-- source:
--   Standard unit-edge metric-graph convention: Nicholas Touikan, On geodesic ray bundles in hyperbolic groups, Proceedings of the American Mathematical Society 146 (2018), 4165–4173, Section 2. https://arxiv.org/abs/1706.01979 The present construction and supporting lemmas are proved in the supplied Lean development; these targets are not assigned numbered theorem attributions in that paper.

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry

universe u

theorem RayBundle.GraphRealization.integer_distance_vertex {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (p : RayBundle.GraphRealization T hT e)
    (v : V) (n : ℕ) (hn : dist p (RayBundle.GraphRealization.vertex T hT e v) = (n : ℝ)) :
    ∃ w, p = RayBundle.GraphRealization.vertex T hT e w := by sorry
