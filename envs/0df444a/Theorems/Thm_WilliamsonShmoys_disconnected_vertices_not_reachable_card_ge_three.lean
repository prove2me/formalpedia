-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices_not_reachable_card_ge_three
-- name    : WilliamsonShmoys.disconnected_vertices_not_reachable_card_ge_three
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:37:19.243865+00:00
-- url     : https://prove2.me/theorems/8b4451c8-ec84-42fc-961e-d191534c0363
-- title:
--   A nontrivial disconnected graph has an unreachable pair
-- statement:
--   A disconnected graph on a finite vertex type of cardinality at least three has a pair of vertices that are not reachable from one another. The cardinality condition is retained from the target; the pair extraction follows directly from connectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.disconnected_vertices_not_reachable_card_ge_three
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ u v : V, ¬ K.Reachable u v := by sorry
