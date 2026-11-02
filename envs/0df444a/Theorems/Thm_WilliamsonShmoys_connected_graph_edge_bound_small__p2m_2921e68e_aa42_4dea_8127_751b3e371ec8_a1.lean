-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_graph_edge_bound_small__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
-- name    : WilliamsonShmoys.connected_graph_edge_bound_small__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:41:45.550922+00:00
-- url     : https://prove2.me/theorems/65988c9c-958c-4922-a284-40b1f8cd618a
-- title:
--   Connected simple graph edge bound below three vertices
-- statement:
--   A finite connected simple graph with fewer than three vertices satisfies the edge-count inequality by the generic simple-graph edge bound; connectivity excludes the empty vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_graph_edge_bound_small__p2m_2921e68e_aa42_4dea_8127_751b3e371ec8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconn : G.Connected)
    (hcard : Fintype.card V < 3) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 3 ≤ 3 * Fintype.card V := by sorry
