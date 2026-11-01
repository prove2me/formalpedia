-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_euler_face_count__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1
-- name    : WilliamsonShmoys.connected_planar_simple_graph_euler_face_count__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:08:03.93371+00:00
-- url     : https://prove2.me/theorems/ffda1de2-69a6-49c0-ac58-96bd14962417
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with the given planar drawing has a natural-number face count satisfying Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_simple_graph_euler_face_count__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hconn : K.Connected) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      ∃ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2) := by sorry
