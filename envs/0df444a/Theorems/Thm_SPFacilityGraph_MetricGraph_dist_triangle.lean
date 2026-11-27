-- Prove2me | Theorems.Thm_SPFacilityGraph_MetricGraph_dist_triangle
-- name    : SPFacilityGraph.MetricGraph.dist_triangle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-26T23:11:20.42736+00:00
-- url     : https://prove2.me/theorems/47bf112a-3289-45c6-b2c9-6eae52a0b3f5
-- title:
--   Triangle inequality for the graph distance $d_G$
-- statement:
--   Let $G\subseteq\mathbb R^k$ be a straight-edge metric graph with graph distance $d_G$ (the infimum of polygonal lengths of walks along the edges). For all $x,y,z\in G$,
--
--   $$
--   d_G(x,z)\;\le\;d_G(x,y)+d_G(y,z).
--   $$
--
--   This is the triangle inequality for the graph distance, one of the axioms making $d_G$ a metric on $G$ as asserted in the source.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092, Section 2.1, p.4 (graph distance d_G: the minimum length of a path in G; a metric on G)

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_dist

set_option autoImplicit false

namespace SPFacilityGraph

theorem MetricGraph.dist_triangle {k : ℕ} (G : MetricGraph k) (x y z : G.Pt) :
    G.dist x z ≤ G.dist x y + G.dist y z := by sorry

end SPFacilityGraph
