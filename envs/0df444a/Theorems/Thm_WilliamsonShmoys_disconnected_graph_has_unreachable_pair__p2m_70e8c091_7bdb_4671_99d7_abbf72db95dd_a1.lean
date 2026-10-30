-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_graph_has_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
-- name    : WilliamsonShmoys.disconnected_graph_has_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T19:03:06.799954+00:00
-- url     : https://prove2.me/theorems/c44ecd5d-b27c-4fd6-98af-d19a8f1230ad
-- title:
--   Disconnected graphs have an unreachable pair
-- statement:
--   A disconnected graph contains a pair of vertices with no path between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_graph_has_unreachable_pair__p2m_70e8c091_7bdb_4671_99d7_abbf72db95dd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdis : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by sorry
