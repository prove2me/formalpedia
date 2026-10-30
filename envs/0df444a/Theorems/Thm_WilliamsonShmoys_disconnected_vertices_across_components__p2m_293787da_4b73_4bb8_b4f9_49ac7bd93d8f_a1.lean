-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices_across_components__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a1
-- name    : WilliamsonShmoys.disconnected_vertices_across_components__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T20:18:08.444+00:00
-- url     : https://prove2.me/theorems/f7e3ab3e-6357-44c1-a42d-50faf333009c
-- title:
--   A disconnected graph has vertices in distinct components
-- statement:
--   Nonconnectivity yields two distinct vertices that are not connected by a path.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_vertices_across_components__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdis : ¬ G.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Reachable u v := by sorry
