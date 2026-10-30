-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices_across_components__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a1
-- name    : WilliamsonShmoys.disconnected_vertices_across_components__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T00:57:06.191086+00:00
-- url     : https://prove2.me/theorems/ae673dae-f9a2-497c-af13-d1dc2e04e17b
-- title:
--   Distinct vertices in different connected components
-- statement:
--   Every disconnected finite graph has distinct vertices that are not connected by a walk. This removes the vertex-selection step from the parent proof. It follows directly by unfolding the definition of connectedness; a reachable vertex is reachable from itself, so the selected vertices must be distinct.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_vertices_across_components__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDisconnected : ¬ K.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Reachable u v := by sorry
