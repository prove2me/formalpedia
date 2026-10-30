-- Prove2me | Theorems.Thm_WilliamsonShmoys_delete_edge_path_connected__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1
-- name    : WilliamsonShmoys.delete_edge_path_connected__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:21:12.297425+00:00
-- url     : https://prove2.me/theorems/5a8b9ec1-c262-427b-9a6a-a4ab7cb1376e
-- title:
--   A surviving path across a deleted edge preserves connectedness
-- statement:
--   For a connected finite graph, if the endpoints of a deleted edge remain reachable after deletion, then the resulting graph is connected. Replace any use of the deleted edge in a path by the surviving endpoint path. The parent applies this only to an added edge and uses the first child to rule out the resulting smaller connected supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false
open SimpleGraph

theorem WilliamsonShmoys.delete_edge_path_connected__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1
    {V : Type} [Fintype V] [Nonempty V]
    (H : SimpleGraph V) (u v : V)
    (hconn : H.Connected)
    (hpath : (H.deleteEdges {s(u, v)}).Reachable u v) :
    (H.deleteEdges {s(u, v)}).Connected := by sorry
