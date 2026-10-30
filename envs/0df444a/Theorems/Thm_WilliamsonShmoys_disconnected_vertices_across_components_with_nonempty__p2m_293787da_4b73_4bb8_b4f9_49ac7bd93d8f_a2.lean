-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices_across_components_with_nonempty__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a2
-- name    : WilliamsonShmoys.disconnected_vertices_across_components_with_nonempty__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:05:41.85143+00:00
-- url     : https://prove2.me/theorems/08982a3d-46a7-4ab9-bd6e-0bba8e7a728d
-- title:
--   A nonempty disconnected graph has distinct unreachable vertices
-- statement:
--   If the finite vertex type has at least three elements and the graph is disconnected, then some two distinct vertices are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_vertices_across_components_with_nonempty__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Reachable u v := by sorry
