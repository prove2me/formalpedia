-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_supergraph_edge_count__p2m_33702fa3_4ca0_4ee2_9d3c_676a8b8ff565_a1
-- name    : WilliamsonShmoys.drawable_graph_has_triangulated_supergraph_edge_count__p2m_33702fa3_4ca0_4ee2_9d3c_676a8b8ff565_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:23:52.883556+00:00
-- url     : https://prove2.me/theorems/8b622a66-c72a-42ac-86d2-b24f5cfdd6f7
-- title:
--   Triangulated drawable supergraph edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulated_supergraph_edge_count__p2m_33702fa3_4ca0_4ee2_9d3c_676a8b8ff565_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, ∃ dK : DecidableRel K.Adj,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H ≤ K ∧
      (letI : DecidableRel K.Adj := dK;
       3 * Fintype.card V - 6 = K.edgeFinset.card) := by sorry
