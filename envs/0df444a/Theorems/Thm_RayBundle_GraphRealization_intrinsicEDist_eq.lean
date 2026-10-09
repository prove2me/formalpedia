-- Prove2me | Theorems.Thm_RayBundle_GraphRealization_intrinsicEDist_eq
-- name    : RayBundle.GraphRealization.intrinsicEDist_eq
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-10-08T18:56:58.839871+00:00
-- url     : https://prove2.me/theorems/6283abac-8aeb-4ef6-bf5c-837bdc01f27b
-- title:
--   The unit-edge realization metric equals the intrinsic continuous-path metric
-- statement:
--   Let $T$ be a connected simple graph on a vertex type $V$, with an explicit edge enumeration $e:\mathbb N\simeq E(T)$; in particular its edge set is countably infinite. Let $|T|_e$ be the unit-edge metric realization formed by successive isometric interval attachments and their metric inductive limit. Write $\iota:V\to|T|_e$ for its vertex map and $\epsilon_n:[0,1]\to|T|_e$ for its $n$th edge map.
--
--   For all $p,q\in|T|_e$, $$\inf_{\gamma:[0,1]\to|T|_e\atop \gamma(0)=p,\,\gamma(1)=q}\operatorname{Length}(\gamma)=d(p,q).$$ The infimum ranges over all continuous endpoint paths, and length is the metric total variation with values in $[0,\infty]$. The formal equality is expressed using extended distance.
-- source:
--   Standard unit-edge metric-graph convention: Nicholas Touikan, On geodesic ray bundles in hyperbolic groups, Proceedings of the American Mathematical Society 146 (2018), 4165–4173, Section 2. https://arxiv.org/abs/1706.01979 The present construction and supporting lemmas are proved in the supplied Lean development; these targets are not assigned numbered theorem attributions in that paper.

import Definitions.Def_RayBundle_UnitEdgeGraphGeometry

universe u

theorem RayBundle.GraphRealization.intrinsicEDist_eq {V : Type*} (T : SimpleGraph V)
    (hT : T.Connected) (e : ℕ ≃ T.edgeSet) (p q : RayBundle.GraphRealization T hT e) :
    RayBundle.intrinsicEDist p q = edist p q := by sorry
