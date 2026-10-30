-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices_across_components_card_ge_three__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a2
-- name    : WilliamsonShmoys.disconnected_vertices_across_components_card_ge_three__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:22:55.066123+00:00
-- url     : https://prove2.me/theorems/0c7a2e4f-7592-47b4-9a07-c3f5e09bb4ed
-- title:
--   Distinct unreachable vertices in a nonempty disconnected graph
-- statement:
--   If a finite graph has at least three vertices and is disconnected, it has a distinct pair of unreachable vertices. The cardinality bound ensures the vertex type is nonempty, so disconnectedness cannot arise solely from the empty-vertex case. After establishing nonemptiness, unfold `Connected` and select a pair that is not reachable; reflexivity of reachability ensures the pair is distinct.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_vertices_across_components_card_ge_three__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Reachable u v := by sorry
