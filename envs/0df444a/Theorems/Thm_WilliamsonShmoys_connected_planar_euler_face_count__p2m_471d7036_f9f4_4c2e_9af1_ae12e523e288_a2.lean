-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a2
-- name    : WilliamsonShmoys.connected_planar_euler_face_count__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:33:56.721873+00:00
-- url     : https://prove2.me/theorems/2a371ccd-5646-41c6-a0b9-de967ec156bd
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   This child supplies the face count needed by the parent: a finite connected graph with the given crossing-free drawing has a natural number f satisfying Euler's equation V + f = E + 2. Its source is Euler's formula for a connected plane graph. A proof route is to establish the formula for a spanning tree, then add the remaining drawn edges one at a time, showing each added edge increases the number of complementary regions by one. The child preserves connectedness and the drawing hypothesis; formalizing the topological region-counting facts from the supplied arc definition is part of its proof. The parent uses this child's f and equation directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_euler_face_count__p2m_471d7036_f9f4_4c2e_9af1_ae12e523e288_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     ∃ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2) := by sorry
