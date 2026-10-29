-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_graph_edge_count_lower_bound__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3
-- name    : WilliamsonShmoys.connected_graph_edge_count_lower_bound__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:52:38.838984+00:00
-- url     : https://prove2.me/theorems/c7b09d10-c765-46b0-922f-6c383e7b8472
-- title:
--   Connected finite graphs have at least one fewer edge than vertices
-- statement:
--   A finite connected simple graph has at least |V| − 1 edges. This supplies the numerical bound independently of the planar drawing. A proof can take a spanning tree of the connected graph, use its |V| − 1 edges, and include those edges in the graph. Connectedness handles the empty-vertex boundary case, where the claimed inequality is also valid.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_graph_edge_count_lower_bound__p2m_367e7ff6_f47c_4801_a657_f77b95acb1d0_a3
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (hConn : H.Connected) :
    Fintype.card V ≤ H.edgeSet.ncard + 1 := by sorry
