-- Prove2me | Theorems.Thm_SPFacilityGraph_MetricGraph_dist_comm
-- name    : SPFacilityGraph.MetricGraph.dist_comm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:11:34.596565+00:00
-- url     : https://prove2.me/theorems/0fb1d40b-5c32-5bf2-ae4c-247612b1f8f6
-- title:
--   Symmetry of the graph distance $d_G$
-- statement:
--   Let $G\subseteq\mathbb R^k$ be a straight-edge metric graph with graph distance $d_G$ (the infimum of polygonal lengths of walks along the edges). For all $x,y\in G$,
--
--   $$
--   d_G(x,y)=d_G(y,x).
--   $$
--
--   This is the symmetry of the graph distance, one of the axioms making $d_G$ a metric on $G$ as asserted in the source.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092, Section 2.1, p.4 (graph distance d_G: the minimum length of a path in G; a metric on G)

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_dist

set_option autoImplicit false

namespace SPFacilityGraph

theorem MetricGraph.dist_comm {k : ℕ} (G : MetricGraph k) (x y : G.Pt) :
    G.dist x y = G.dist y x := by sorry

end SPFacilityGraph
