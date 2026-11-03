-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:16:37.555544+00:00
-- url     : https://prove2.me/theorems/c59fe07e-0bca-4d4e-9b09-8335007f2f58
-- title:
--   Edge bound for a connected planar graph
-- statement:
--   A connected finite simple graph with the attached crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
