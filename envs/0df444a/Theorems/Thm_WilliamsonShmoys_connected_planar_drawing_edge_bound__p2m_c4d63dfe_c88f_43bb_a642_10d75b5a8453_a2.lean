-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:55:23.627898+00:00
-- url     : https://prove2.me/theorems/7d4137c4-15dc-451a-ba6d-47dc1f35dd68
-- title:
--   Euler edge bound for a connected graph with a planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a drawing satisfying the stated nonintersection conditions has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
