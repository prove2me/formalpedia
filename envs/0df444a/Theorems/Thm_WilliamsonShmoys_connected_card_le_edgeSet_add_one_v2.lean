-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_card_le_edgeSet_add_one_v2
-- name    : WilliamsonShmoys.connected_card_le_edgeSet_add_one_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:33:38.44693+00:00
-- url     : https://prove2.me/theorems/e7e7ea94-cfb8-42a7-be8c-ad63b11a4b94
-- title:
--   Connected graph edge count lower bound
-- statement:
--   A finite connected graph has at least one fewer edge than vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_card_le_edgeSet_add_one_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hConnected : L.Connected) :
    Fintype.card V ≤ L.edgeSet.ncard + 1 := by sorry
