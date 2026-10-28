-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound_add_six
-- name    : WilliamsonShmoys_connected_planar_edge_count_bound_add_six
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:03:44.985729+00:00
-- url     : https://prove2.me/theorems/5d3976a5-a1f6-4e2e-8ef2-1c6745986163
-- title:
--   Additive form of the connected planar edge bound
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges, expressed without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys_connected_planar_edge_count_bound_add_six
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
