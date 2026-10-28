-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_nonacyclic_card_le_edge_ncard
-- name    : WilliamsonShmoys.connected_nonacyclic_card_le_edge_ncard
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:36:59.266422+00:00
-- url     : https://prove2.me/theorems/0e6f03ea-46ab-4ca9-8d33-4353be3ebe68
-- title:
--   A connected cyclic graph has at least as many edges as vertices
-- statement:
--   A finite connected graph containing a cycle has at least as many edges as vertices: a spanning tree has one fewer edge than vertices, and the cycle requires an additional edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_nonacyclic_card_le_edge_ncard
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hCyclic : ¬ G.IsAcyclic) :
    Fintype.card V ≤ G.edgeSet.ncard := by sorry
