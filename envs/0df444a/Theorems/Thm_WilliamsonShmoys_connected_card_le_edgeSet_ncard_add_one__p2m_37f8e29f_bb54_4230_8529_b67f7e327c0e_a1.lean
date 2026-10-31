-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_card_le_edgeSet_ncard_add_one__p2m_37f8e29f_bb54_4230_8529_b67f7e327c0e_a1
-- name    : WilliamsonShmoys.connected_card_le_edgeSet_ncard_add_one__p2m_37f8e29f_bb54_4230_8529_b67f7e327c0e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:05:56.676809+00:00
-- url     : https://prove2.me/theorems/77a6911c-9717-4005-9ce3-19973e54a5df
-- title:
--   Edge count bound for a finite connected graph
-- statement:
--   A finite connected simple graph has at least one fewer edge than vertices. This is the sole graph-theoretic obligation needed by the parent; for a nonempty vertex type, prove it by taking a spanning tree and using the tree edge-count formula. For the empty type the inequality is immediate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_card_le_edgeSet_ncard_add_one__p2m_37f8e29f_bb54_4230_8529_b67f7e327c0e_a1
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hconn : G.Connected) :
    Fintype.card V ≤ G.edgeSet.ncard + 1 := by sorry
