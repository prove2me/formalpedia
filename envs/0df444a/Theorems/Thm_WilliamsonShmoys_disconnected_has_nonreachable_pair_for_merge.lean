-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_nonreachable_pair_for_merge
-- name    : WilliamsonShmoys.disconnected_has_nonreachable_pair_for_merge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:33:34.947238+00:00
-- url     : https://prove2.me/theorems/8ba08773-c6fc-4704-b118-56ac16c8e7ca
-- title:
--   Extract an unreachable pair from disconnectedness
-- statement:
--   A finite graph with at least three vertices that is disconnected has a pair of vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.disconnected_has_nonreachable_pair_for_merge
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by sorry
