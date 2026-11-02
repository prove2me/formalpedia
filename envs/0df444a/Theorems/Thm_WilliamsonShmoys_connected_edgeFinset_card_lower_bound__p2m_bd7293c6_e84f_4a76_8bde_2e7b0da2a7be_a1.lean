-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edgeFinset_card_lower_bound__p2m_bd7293c6_e84f_4a76_8bde_2e7b0da2a7be_a1
-- name    : WilliamsonShmoys.connected_edgeFinset_card_lower_bound__p2m_bd7293c6_e84f_4a76_8bde_2e7b0da2a7be_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:55:51.541032+00:00
-- url     : https://prove2.me/theorems/b4e8c4d0-872d-4f1c-8019-7f5b608a64e6
-- title:
--   Connected graphs have at least vertices minus one edges
-- statement:
--   Every finite connected graph has at least one fewer edge than vertices. This removes the spanning-tree/edge-count argument from the parent; the remaining core obligation is proving this bound, for example by finding a spanning tree, counting its edges, and comparing its edges with those of the graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.connected_edgeFinset_card_lower_bound__p2m_bd7293c6_e84f_4a76_8bde_2e7b0da2a7be_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : L.Connected) :
    Fintype.card V - 1 ≤ (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) := by
  sorry
