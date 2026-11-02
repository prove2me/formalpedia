-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_simple_planar_edge_bound__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1
-- name    : WilliamsonShmoys.connected_simple_planar_edge_bound__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:49:42.987201+00:00
-- url     : https://prove2.me/theorems/b23772a1-7f55-4be6-b745-ebb5a4e685d3
-- title:
--   Simple planar edge bound
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied crossing-free drawing has at most 3n − 6 edges, stated without truncated natural subtraction. A proof route is to combine Euler’s formula with the lower bound of three boundary incidences per face, counting bridge incidences with multiplicity; the three-vertex boundary case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_simple_planar_edge_bound__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : HasPlanarDrawingOn J)
    (hconn : ∀ u v : V, Nonempty (J.Walk u v))
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    J.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
