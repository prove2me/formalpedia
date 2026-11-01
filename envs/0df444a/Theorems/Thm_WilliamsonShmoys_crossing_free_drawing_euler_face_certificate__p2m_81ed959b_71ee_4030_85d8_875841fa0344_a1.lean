-- Prove2me | Theorems.Thm_WilliamsonShmoys_crossing_free_drawing_euler_face_certificate__p2m_81ed959b_71ee_4030_85d8_875841fa0344_a1
-- name    : WilliamsonShmoys.crossing_free_drawing_euler_face_certificate__p2m_81ed959b_71ee_4030_85d8_875841fa0344_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:28:36.730223+00:00
-- url     : https://prove2.me/theorems/13bbb924-e4bd-450d-a0aa-ab4d555ea2ad
-- title:
--   Euler face certificate for a crossing-free drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing, there is a natural-number face count satisfying Euler’s equation and the lower bound on total face-boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.crossing_free_drawing_euler_face_certificate__p2m_81ed959b_71ee_4030_85d8_875841fa0344_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      H.edgeSet.ncard + f = Fintype.card V + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by sorry
