-- Prove2me | Theorems.Thm_RayBundle_GraphRealization_covered
-- name    : RayBundle.GraphRealization.covered
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-10-08T18:56:56.145985+00:00
-- url     : https://prove2.me/theorems/4c992d69-5d07-449c-b368-8b620f63458a
-- title:
--   Vertices and realized edges cover the unit-edge graph realization
-- statement:
--   Let $T$ be a connected simple graph on a vertex type $V$, with an explicit edge enumeration $e:\mathbb N\simeq E(T)$; in particular its edge set is countably infinite. Let $|T|_e$ be the unit-edge metric realization formed by successive isometric interval attachments and their metric inductive limit. Write $\iota:V\to|T|_e$ for its vertex map and $\epsilon_n:[0,1]\to|T|_e$ for its $n$th edge map.
--
--   Every $p\in|T|_e$ is either $\iota(v)$ for some vertex $v$, or $\epsilon_n(t)$ for some $n\in\mathbb N$ and $t\in[0,1]$. The inductive limit here is taken without a metric completion.
-- source:
--   Standard unit-edge metric-graph convention: Nicholas Touikan, On geodesic ray bundles in hyperbolic groups, Proceedings of the American Mathematical Society 146 (2018), 4165–4173, Section 2. https://arxiv.org/abs/1706.01979 The present construction and supporting lemmas are proved in the supplied Lean development; these targets are not assigned numbered theorem attributions in that paper.

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry

universe u

theorem RayBundle.GraphRealization.covered {V : Type u} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (p : RayBundle.GraphRealization T hT e) :
    (∃ v, p = RayBundle.GraphRealization.vertex T hT e v) ∨ ∃ n t, p = RayBundle.GraphRealization.edge T hT e n t := by sorry
