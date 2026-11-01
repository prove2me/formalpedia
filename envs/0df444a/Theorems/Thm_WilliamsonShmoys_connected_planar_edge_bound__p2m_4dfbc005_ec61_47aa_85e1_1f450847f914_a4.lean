-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:18:10.540391+00:00
-- url     : https://prove2.me/theorems/33d2e955-2f8d-4bbc-bacc-303875c5504a
-- title:
--   Euler edge bound for connected planar graphs
-- statement:
--   A connected simple graph with at least three vertices and the supplied planar drawing satisfies the Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_4dfbc005_ec61_47aa_85e1_1f450847f914_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : M.Connected)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
