-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edge_card_lower_bound__p2m_a78a6ebd_f14e_4d5e_887a_7bf11c56fcc6_a1
-- name    : WilliamsonShmoys.connected_edge_card_lower_bound__p2m_a78a6ebd_f14e_4d5e_887a_7bf11c56fcc6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:15:38.897288+00:00
-- url     : https://prove2.me/theorems/eb53c828-9e2b-496e-98fa-e97d32d77695
-- title:
--   Connected finite graphs have at least |V| − 1 edges
-- statement:
--   A finite connected simple graph has at least one fewer edge than vertices. This is the graph-theoretic fact needed to produce the natural-number witness in the parent’s arithmetic equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_edge_card_lower_bound__p2m_a78a6ebd_f14e_4d5e_887a_7bf11c56fcc6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected) :
    Fintype.card V ≤ H.edgeFinset.card + 1 := by sorry
