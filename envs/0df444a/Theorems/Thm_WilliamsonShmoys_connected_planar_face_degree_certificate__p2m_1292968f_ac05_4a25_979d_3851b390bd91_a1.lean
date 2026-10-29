-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_degree_certificate__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
-- name    : WilliamsonShmoys.connected_planar_face_degree_certificate__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:42:39.818401+00:00
-- url     : https://prove2.me/theorems/1970b9e6-74d7-4a12-8715-da9084da0982
-- title:
--   Euler face-degree certificate for connected planar drawings
-- statement:
--   A connected simple planar drawing with at least three vertices has finite face-boundary data whose total length is twice the edge count, whose every face has boundary length at least three, and which satisfies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_planar_face_degree_certificate__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConn : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ (m : ℕ) (boundary : Fin m → ℕ),
      (∑ i : Fin m, boundary i) = 2 * G.edgeSet.ncard ∧
      3 * m ≤ ∑ i : Fin m, boundary i ∧
      Fintype.card V + m = G.edgeSet.ncard + 2 := by sorry
