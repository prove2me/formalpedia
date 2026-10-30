-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices_not_connected__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2
-- name    : WilliamsonShmoys.disconnected_vertices_not_connected__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T08:46:30.68478+00:00
-- url     : https://prove2.me/theorems/f82c11b4-a5d3-45af-ab2a-03f047e7ba4d
-- title:
--   Disconnectedness gives vertices with no walk
-- statement:
--   If a graph is not connected, it has a pair of vertices with no walk between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_vertices_not_connected__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDisc : ¬ G.Connected) :
    ∃ u v : V, ¬ Nonempty (G.Walk u v) := by sorry
