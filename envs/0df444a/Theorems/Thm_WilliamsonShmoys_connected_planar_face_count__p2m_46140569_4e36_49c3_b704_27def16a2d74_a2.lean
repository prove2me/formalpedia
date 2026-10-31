-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_count__p2m_46140569_4e36_49c3_b704_27def16a2d74_a2
-- name    : WilliamsonShmoys.connected_planar_face_count__p2m_46140569_4e36_49c3_b704_27def16a2d74_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:19:20.887449+00:00
-- url     : https://prove2.me/theorems/714e0d6d-4b4e-4713-bad3-a0723dae3971
-- title:
--   Euler relation and face-boundary count for a connected planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has a natural-number face count satisfying Euler’s relation and the total face-boundary-length inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_face_count__p2m_46140569_4e36_49c3_b704_27def16a2d74_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ F : ℕ,
      Fintype.card V + F = H.edgeSet.ncard + 2 ∧
      3 * F <= 2 * H.edgeSet.ncard := by sorry
