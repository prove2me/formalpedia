-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_nonreachable_pair__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a1
-- name    : WilliamsonShmoys.disconnected_planar_drawing_has_nonreachable_pair__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:52:27.070292+00:00
-- url     : https://prove2.me/theorems/66ce912a-4f34-4918-ae6a-49dc5ecf1e8d
-- title:
--   Disconnectedness yields a nonreachable pair
-- statement:
--   A disconnected finite graph with at least three vertices has a pair of vertices in different connected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_planar_drawing_has_nonreachable_pair__p2m_e7f58e98_9faf_49a6_bc58_50960cb4a0da_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by
  sorry
