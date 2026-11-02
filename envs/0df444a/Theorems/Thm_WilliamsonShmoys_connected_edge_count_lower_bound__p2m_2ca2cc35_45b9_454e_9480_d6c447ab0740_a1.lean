-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edge_count_lower_bound__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1
-- name    : WilliamsonShmoys.connected_edge_count_lower_bound__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:35:36.806376+00:00
-- url     : https://prove2.me/theorems/ea748d00-b8a2-455d-9c4a-2848fb6ef09a
-- title:
--   Connected graph edge lower bound
-- statement:
--   Every finite connected graph has at least |V|−1 edges. A spanning tree gives an independent proof route; the statement also holds for the empty-vertex boundary if connectedness is vacuous there.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_edge_count_lower_bound__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (hconn : H.Connected) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     Fintype.card V ≤ H.edgeFinset.card + 1) := by sorry
