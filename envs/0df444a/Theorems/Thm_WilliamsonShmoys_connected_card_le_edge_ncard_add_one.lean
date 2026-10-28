-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_card_le_edge_ncard_add_one
-- name    : WilliamsonShmoys.connected_card_le_edge_ncard_add_one
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:11:22.041752+00:00
-- url     : https://prove2.me/theorems/0f251f57-96b1-4498-b64c-e81d3aea9f52
-- title:
--   Connected finite graphs have at least one fewer edge than vertices
-- statement:
--   Every finite connected simple graph has at least one fewer edge than vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_card_le_edge_ncard_add_one
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hconn : L.Connected) :
    Fintype.card V ≤ L.edgeSet.ncard + 1 := by sorry
