-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_has_face_length_certificate__p2m_1fede0fd_ca75_4d2a_8cf1_d73a70c51443_a1
-- name    : WilliamsonShmoys.drawing_has_face_length_certificate__p2m_1fede0fd_ca75_4d2a_8cf1_d73a70c51443_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:25:19.128658+00:00
-- url     : https://prove2.me/theorems/8099996c-49f1-4f0a-8c18-5243a138e1ea
-- title:
--   Face-length certificate from a connected planar drawing
-- statement:
--   A connected simple graph with at least three vertices and the supplied crossing-free drawing has a finite list of facial boundary-walk lengths satisfying Euler’s formula, total boundary length twice the number of edges, and length at least three for every face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.drawing_has_face_length_certificate__p2m_1fede0fd_ca75_4d2a_8cf1_d73a70c51443_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hConn : M.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ faces : List Nat,
      (Fintype.card V : Int) - (M.edgeSet.ncard : Int) + (faces.length : Int) = 2 ∧
      faces.sum = 2 * M.edgeSet.ncard ∧
      ∀ length ∈ faces, 3 <= length := by sorry
