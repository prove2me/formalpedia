-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:35:00.545631+00:00
-- url     : https://prove2.me/theorems/58a4bbec-9b1c-4062-8fb0-876ba124b0f6
-- title:
--   Connected planar edge bound
-- statement:
--   A connected finite simple graph with a planar drawing and at least three vertices has at most 3|V|−6 edges. This is the connected core removed from the parent. A proof route constructs the plane map from the drawing, applies Euler’s formula, and counts face-edge incidences; bridges require care because a face boundary walk may traverse a bridge twice. The remaining obligation is to formalize that map and incidence argument in Lean.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_4ab90c81_e0ae_42fd_86c7_d03618200022_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hconn : N.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    N.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
