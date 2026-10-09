-- Prove2me | Theorems.Thm_RayBundle_GraphRealization_edge_isometry
-- name    : RayBundle.GraphRealization.edge_isometry
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-10-08T18:56:59.788165+00:00
-- url     : https://prove2.me/theorems/f8a2a153-7d69-4f81-a564-a19154645c4c
-- title:
--   Every realized unit edge is an isometric interval
-- statement:
--   Let $T$ be a connected simple graph on a vertex type $V$, with an explicit edge enumeration $e:\mathbb N\simeq E(T)$; in particular its edge set is countably infinite. Let $|T|_e$ be the unit-edge metric realization formed by successive isometric interval attachments and their metric inductive limit. Write $\iota:V\to|T|_e$ for its vertex map and $\epsilon_n:[0,1]\to|T|_e$ for its $n$th edge map.
--
--   For every $n\in\mathbb N$, $\epsilon_n$ is an isometry. Equivalently, $d(\epsilon_n(s),\epsilon_n(t))=|s-t|$ for $s,t\in[0,1]$.
-- source:
--   Standard unit-edge metric-graph convention: Nicholas Touikan, On geodesic ray bundles in hyperbolic groups, Proceedings of the American Mathematical Society 146 (2018), 4165–4173, Section 2. https://arxiv.org/abs/1706.01979 The present construction and supporting lemmas are proved in the supplied Lean development; these targets are not assigned numbered theorem attributions in that paper.

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry

universe u

theorem RayBundle.GraphRealization.edge_isometry {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (n : ℕ) : Isometry (RayBundle.GraphRealization.edge T hT e n) := by sorry
