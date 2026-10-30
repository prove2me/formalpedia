-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_graph_edge_lower_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
-- name    : WilliamsonShmoys.connected_graph_edge_lower_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:14:42.695753+00:00
-- url     : https://prove2.me/theorems/a3d3ef79-7381-4680-97d0-c89fad955099
-- title:
--   Connected finite graphs have at least |V| - 1 edges
-- statement:
--   Every finite connected simple graph has at least one fewer edge than vertices. This supplies the target's lower-bound conjunct without using the drawing or the size hypothesis. The concrete proof route is to obtain a spanning tree and count its edges, or induct on the number of vertices using a leaf of that tree. The claim also covers the one-vertex connected graph, where the inequality is equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem WilliamsonShmoys.connected_graph_edge_lower_bound__p2m_4d55918f_bbf7_4f10_a854_239f6af3f8f1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected) :
    Fintype.card V <= K.edgeSet.ncard + 1 := by sorry
