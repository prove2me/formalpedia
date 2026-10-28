-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_graph_edge_count_lower_bound__p2m_2aa9d4d8_ca19_4a3e_94b2_47d01f3eb35e_a1
-- name    : WilliamsonShmoys.connected_graph_edge_count_lower_bound__p2m_2aa9d4d8_ca19_4a3e_94b2_47d01f3eb35e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:26:41.973096+00:00
-- url     : https://prove2.me/theorems/740b35d6-a6d3-4616-b2a6-a8741d3eb01a
-- title:
--   Connected graphs have enough edges for the witness
-- statement:
--   Every finite connected simple graph has at least one fewer edge than vertices. This follows from a spanning tree; pinned Mathlib includes the corresponding connected-graph cardinality bound, with finite-cardinality conversions needed for this statement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_graph_edge_count_lower_bound__p2m_2aa9d4d8_ca19_4a3e_94b2_47d01f3eb35e_a1
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hG : G.Connected) :
    Fintype.card V ≤ G.edgeSet.ncard + 1 := by sorry
