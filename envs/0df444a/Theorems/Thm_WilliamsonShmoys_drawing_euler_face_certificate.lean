-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_euler_face_certificate
-- name    : WilliamsonShmoys.drawing_euler_face_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:29:11.950811+00:00
-- url     : https://prove2.me/theorems/7c5eea9e-4239-4074-b13c-15b8482d92aa
-- title:
--   Euler face certificate from a crossing-free drawing
-- statement:
--   For a connected simple graph on at least three vertices with the supplied crossing-free drawing, there is a number of faces satisfying Euler’s formula and the lower bound of three on the total facial boundary length. Counting each edge twice across facial boundaries gives the stated inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawing_euler_face_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ F : ℕ,
      Fintype.card V + F = K.edgeSet.ncard + 2 ∧
      3 * F <= 2 * K.edgeSet.ncard := by sorry
