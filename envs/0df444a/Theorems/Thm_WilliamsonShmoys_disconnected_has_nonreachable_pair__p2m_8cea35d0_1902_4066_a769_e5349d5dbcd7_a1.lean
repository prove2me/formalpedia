-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_nonreachable_pair__p2m_8cea35d0_1902_4066_a769_e5349d5dbcd7_a1
-- name    : WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_8cea35d0_1902_4066_a769_e5349d5dbcd7_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:41.946393+00:00
-- url     : https://prove2.me/theorems/ddad11f4-2b8e-42c8-afbb-082535f53467
-- title:
--   Disconnected graphs contain a non-reachable pair
-- statement:
--   A disconnected finite graph has two vertices that are not connected by a path. The parent uses this to select the pair for the drawing extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_has_nonreachable_pair__p2m_8cea35d0_1902_4066_a769_e5349d5dbcd7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hDisconnected : ¬ H.Connected) :
    ∃ u v : V, ¬ H.Reachable u v := by sorry
