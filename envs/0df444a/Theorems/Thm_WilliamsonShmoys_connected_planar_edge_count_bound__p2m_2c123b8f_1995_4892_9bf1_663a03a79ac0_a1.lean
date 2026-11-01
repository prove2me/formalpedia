-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
-- name    : WilliamsonShmoys.connected_planar_edge_count_bound__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:48.342173+00:00
-- url     : https://prove2.me/theorems/4f0f4017-69c8-49f6-a405-0b1a215ecea7
-- title:
--   Edge-count bound for connected planar drawings
-- statement:
--   Every connected simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_bound__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected) (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
