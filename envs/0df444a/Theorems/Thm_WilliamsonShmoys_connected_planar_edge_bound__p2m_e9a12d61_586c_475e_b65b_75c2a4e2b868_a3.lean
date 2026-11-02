-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_e9a12d61_586c_475e_b65b_75c2a4e2b868_a3
-- name    : WilliamsonShmoys_connected_planar_edge_bound__p2m_e9a12d61_586c_475e_b65b_75c2a4e2b868_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:36:55.405511+00:00
-- url     : https://prove2.me/theorems/0b4d7427-fa64-4726-8753-b179ad4988fb
-- title:
--   Euler edge bound for connected graphs with the given drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a drawing satisfying the exact custom arc conditions has at most 3n−6 edges. This isolates the Euler formula and face-incidence argument, including bridges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_connected_planar_edge_bound__p2m_e9a12d61_586c_475e_b65b_75c2a4e2b868_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
