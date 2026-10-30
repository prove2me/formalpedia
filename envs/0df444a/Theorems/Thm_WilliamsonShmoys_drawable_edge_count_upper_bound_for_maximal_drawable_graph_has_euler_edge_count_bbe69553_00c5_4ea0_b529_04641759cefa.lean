-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_edge_count_upper_bound_for_maximal_drawable_graph_has_euler_edge_count_bbe69553_00c5_4ea0_b529_04641759cefa
-- name    : WilliamsonShmoys.drawable_edge_count_upper_bound_for_maximal_drawable_graph_has_euler_edge_count_bbe69553_00c5_4ea0_b529_04641759cefa
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:06:34.389797+00:00
-- url     : https://prove2.me/theorems/8f624e72-b36c-4406-b7a1-0f72ae53aef9
-- title:
--   Euler upper bound for drawable simple graphs
-- statement:
--   A drawable simple graph on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_edge_count_upper_bound_for_maximal_drawable_graph_has_euler_edge_count_bbe69553_00c5_4ea0_b529_04641759cefa
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
