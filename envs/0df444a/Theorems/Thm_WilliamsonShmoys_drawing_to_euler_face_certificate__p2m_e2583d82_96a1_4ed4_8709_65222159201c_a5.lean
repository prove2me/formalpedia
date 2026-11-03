-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_to_euler_face_certificate__p2m_e2583d82_96a1_4ed4_8709_65222159201c_a5
-- name    : WilliamsonShmoys.drawing_to_euler_face_certificate__p2m_e2583d82_96a1_4ed4_8709_65222159201c_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:03:36.088956+00:00
-- url     : https://prove2.me/theorems/6e5a9dbe-f5b6-4fde-9426-557ef9f6a091
-- title:
--   Extract Euler and face-incidence data from a drawing with at least three vertices
-- statement:
--   For a finite simple connected graph on at least three vertices, a crossing-free drawing supplies a face count satisfying Euler’s equation and the face-incidence bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.drawing_to_euler_face_certificate__p2m_e2583d82_96a1_4ed4_8709_65222159201c_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : (L : SimpleGraph V) -> DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    ∃ f : Nat,
      Fintype.card V + f = K.edgeFinset.card + 2 ∧
      3 * f <= 2 * K.edgeFinset.card := by sorry
