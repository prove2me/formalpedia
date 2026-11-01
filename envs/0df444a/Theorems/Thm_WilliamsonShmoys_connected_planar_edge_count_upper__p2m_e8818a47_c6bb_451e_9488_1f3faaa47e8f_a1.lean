-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a1
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:59:17.661655+00:00
-- url     : https://prove2.me/theorems/b8269eb8-92ab-410e-b303-8b7e95b6e6b3
-- title:
--   Connected planar simple graph edge bound
-- statement:
--   A connected finite simple graph with the given crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_upper__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  sorry
