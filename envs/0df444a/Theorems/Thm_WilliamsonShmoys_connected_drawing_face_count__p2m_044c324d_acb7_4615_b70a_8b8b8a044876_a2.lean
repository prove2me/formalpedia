-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_face_count__p2m_044c324d_acb7_4615_b70a_8b8b8a044876_a2
-- name    : WilliamsonShmoys.connected_drawing_face_count__p2m_044c324d_acb7_4615_b70a_8b8b8a044876_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:54:03.428496+00:00
-- url     : https://prove2.me/theorems/ae9acfb5-6e8a-4024-8144-fc4b457004a2
-- title:
--   Euler and face count from a connected planar drawing
-- statement:
--   Every crossing-free drawing of a finite connected simple graph with at least three vertices yields a natural number of faces satisfying Euler's equation and the lower bound on total facial boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_drawing_face_count__p2m_044c324d_acb7_4615_b70a_8b8b8a044876_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * H.edgeFinset.card := by sorry
