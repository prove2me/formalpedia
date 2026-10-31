-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:08.27219+00:00
-- url     : https://prove2.me/theorems/46140569-4e36-49c3-b704-27def16a2d74
-- title:
--   Connected planar edge bound
-- statement:
--   A connected simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_9e7a5396_2787_4caf_938c_608408887b08_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
