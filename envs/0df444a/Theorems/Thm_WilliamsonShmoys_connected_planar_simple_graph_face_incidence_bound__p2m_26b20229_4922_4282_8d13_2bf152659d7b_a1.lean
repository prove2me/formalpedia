-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_face_incidence_bound__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1
-- name    : WilliamsonShmoys.connected_planar_simple_graph_face_incidence_bound__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:08:05.555298+00:00
-- url     : https://prove2.me/theorems/e6b74747-b2b4-4c13-95ec-8e43a6ee5607
-- title:
--   Lower bound on face incidences
-- statement:
--   For a finite connected simple graph with the given planar drawing, any natural number satisfying the Euler face-count equation has total face incidence at least three per face, yielding three times the face count at most twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_simple_graph_face_incidence_bound__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hconn : K.Connected)
    (f : ℕ) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      Fintype.card V + f = K.edgeFinset.card + 2 →
        3 * f ≤ 2 * K.edgeFinset.card) := by sorry
