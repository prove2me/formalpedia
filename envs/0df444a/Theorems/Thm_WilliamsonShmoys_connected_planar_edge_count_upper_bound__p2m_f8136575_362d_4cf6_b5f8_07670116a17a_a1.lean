-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a1
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:14:59.972874+00:00
-- url     : https://prove2.me/theorems/4a8418ba-23c0-49b2-b768-f1b389811726
-- title:
--   Edge bound for connected simple planar graphs
-- statement:
--   A connected simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_f8136575_362d_4cf6_b5f8_07670116a17a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
