-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_accounting__p2m_afce1f76_d895_40f4_a39d_a07d8ca5218a_a3
-- name    : WilliamsonShmoys.connected_planar_drawing_face_accounting__p2m_afce1f76_d895_40f4_a39d_a07d8ca5218a_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:25:32.165373+00:00
-- url     : https://prove2.me/theorems/835bf3db-de81-40c6-b7e0-68fe8c492db0
-- title:
--   Euler face accounting for a connected planar drawing
-- statement:
--   For a finite connected simple graph on at least three vertices with the supplied crossing-free drawing, there is a finite face type satisfying Euler’s equation and the lower bound on total face-boundary incidences. This isolates the topological accounting used by the parent arithmetic reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_face_accounting__p2m_afce1f76_d895_40f4_a39d_a07d8ca5218a_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (F : Type) (hF : Fintype F),
      Fintype.card V + @Fintype.card F hF = H.edgeFinset.card + 2 ∧
      3 * @Fintype.card F hF ≤ 2 * H.edgeFinset.card := by sorry
