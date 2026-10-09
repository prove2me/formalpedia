-- Prove2me | Theorems.Thm_RayBundle_GraphRealization_near_vertex
-- name    : RayBundle.GraphRealization.near_vertex
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-10-08T18:57:02.400768+00:00
-- url     : https://prove2.me/theorems/56bc2eea-3a4e-4f47-af78-7578809ddfc1
-- title:
--   Every point of a unit-edge realization lies within one half of a vertex
-- statement:
--   Let $T$ be a connected simple graph on a vertex type $V$, with an explicit edge enumeration $e:\mathbb N\simeq E(T)$; in particular its edge set is countably infinite. Let $|T|_e$ be the unit-edge metric realization formed by successive isometric interval attachments and their metric inductive limit. Write $\iota:V\to|T|_e$ for its vertex map and $\epsilon_n:[0,1]\to|T|_e$ for its $n$th edge map.
--
--   For every $p\in|T|_e$, there is a vertex $v$ with $$d(p,\iota(v))\le\tfrac12.$$ This is a uniform proximity bound for the vertex image.
-- source:
--   Standard unit-edge metric-graph convention: Nicholas Touikan, On geodesic ray bundles in hyperbolic groups, Proceedings of the American Mathematical Society 146 (2018), 4165–4173, Section 2. https://arxiv.org/abs/1706.01979 The present construction and supporting lemmas are proved in the supplied Lean development; these targets are not assigned numbered theorem attributions in that paper.

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry

universe u

theorem RayBundle.GraphRealization.near_vertex {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (p : RayBundle.GraphRealization T hT e) :
    ∃ v, dist p (RayBundle.GraphRealization.vertex T hT e v) ≤ (1 / 2 : ℝ) := by sorry
