-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_face_count_certificate__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2
-- name    : WilliamsonShmoys.drawing_face_count_certificate__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:42:09.616987+00:00
-- url     : https://prove2.me/theorems/c50fd7db-db60-4155-a74b-9f8219c920fe
-- title:
--   Face-count certificate from a crossing-free drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing, there is a natural number f satisfying the plane Euler relation |V|+f=|E|+2 and the face-incidence bound 3f≤2|E|. This packages the topological conversion from the drawing to plane face walks and their total boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.drawing_face_count_certificate__p2m_dbcd4af9_e055_47f7_910a_a01842a93823_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H)
    (hConn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f <= 2 * H.edgeSet.ncard := by sorry
