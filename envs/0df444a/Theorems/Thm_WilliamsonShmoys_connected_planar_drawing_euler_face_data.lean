-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_data
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_face_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:22:24.343549+00:00
-- url     : https://prove2.me/theorems/8bbd4225-aeff-43ad-bafc-f7c397ab7998
-- title:
--   Euler and boundary data for a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and the supplied crossing-free drawing, there are finitely many face boundary walks whose count satisfies Euler’s equation, whose total length counts each edge side twice, and each of whose lengths is at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.connected_planar_drawing_euler_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ (f : ℕ) (boundaryLength : Fin f → ℕ),
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      (∑ i : Fin f, boundaryLength i) = 2 * K.edgeSet.ncard ∧
      (∀ i, 3 <= boundaryLength i) := by sorry
