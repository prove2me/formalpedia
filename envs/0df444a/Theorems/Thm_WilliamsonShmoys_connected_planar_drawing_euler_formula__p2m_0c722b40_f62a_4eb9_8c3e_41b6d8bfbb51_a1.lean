-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_formula__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_formula__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:49:42.278796+00:00
-- url     : https://prove2.me/theorems/ed960797-d24b-42cc-aa83-38db7a951fc0
-- title:
--   Euler formula for a connected planar drawing
-- statement:
--   For a finite connected simple graph with the supplied crossing-free drawing, its vertex, edge, and face counts satisfy Euler’s formula. The face count is a natural number; the drawing’s connectedness hypothesis is exactly the graph walk-connectivity assumption.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler_formula__p2m_0c722b40_f62a_4eb9_8c3e_41b6d8bfbb51_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : HasPlanarDrawingOn J)
    (hconn : ∀ u v : V, Nonempty (J.Walk u v)) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ f : ℕ, Fintype.card V + f = J.edgeFinset.card + 2 := by sorry
