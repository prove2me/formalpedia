-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_graph_card_le_edge_ncard_add_one__p2m_c14927fd_3bb2_4aa2_8e62_690259e960a9_a1
-- name    : WilliamsonShmoys.connected_graph_card_le_edge_ncard_add_one__p2m_c14927fd_3bb2_4aa2_8e62_690259e960a9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:40:25.697293+00:00
-- url     : https://prove2.me/theorems/2f665cfa-4ffc-419f-9293-2427f3a900ff
-- title:
--   Connected finite graph edge lower bound
-- statement:
--   Every finite connected simple graph has at least one fewer edge than vertices. A spanning-tree argument or induction on the vertex count proves this generic graph fact and supplies the numerical bound used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_graph_card_le_edge_ncard_add_one__p2m_c14927fd_3bb2_4aa2_8e62_690259e960a9_a1
    {V : Type} [Fintype V]
    (K : SimpleGraph V) (hconn : K.Connected) :
    Fintype.card V ≤ K.edgeSet.ncard + 1 := by sorry
