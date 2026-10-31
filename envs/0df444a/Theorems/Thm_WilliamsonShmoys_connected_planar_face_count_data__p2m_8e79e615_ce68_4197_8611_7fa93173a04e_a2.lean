-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_count_data__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
-- name    : WilliamsonShmoys.connected_planar_face_count_data__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:17:10.365514+00:00
-- url     : https://prove2.me/theorems/471d7036-f9f4-4c2e-9af1-ae12e523e288
-- title:
--   Face count data for a connected planar drawing
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has a natural-number face count satisfying Euler’s equation and the aggregate facial-boundary incidence inequality. This isolates the topological counting obligation, including bridges. The size hypothesis excludes the small connected cases where the aggregate inequality may fail.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_face_count_data__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     ∃ f : ℕ,
       Fintype.card V + f = K.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * K.edgeFinset.card) := by sorry
