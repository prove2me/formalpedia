-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_pair_of_not_connected__p2m_d5850897_bb19_4a14_84a1_2d0f5ebfaf1b_a1
-- name    : WilliamsonShmoys.disconnected_pair_of_not_connected__p2m_d5850897_bb19_4a14_84a1_2d0f5ebfaf1b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:12:50.46701+00:00
-- url     : https://prove2.me/theorems/307a49b2-cf45-4016-9a7f-d50dead18583
-- title:
--   Extract an unreachable pair from disconnectedness
-- statement:
--   In a finite vertex type with at least three elements, a disconnected graph has two distinct vertices that are not connected by a path.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.disconnected_pair_of_not_connected__p2m_d5850897_bb19_4a14_84a1_2d0f5ebfaf1b_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDisc : ¬ L.Connected) : ∃ u v : V, u ≠ v ∧ ¬ L.Reachable u v := by sorry
