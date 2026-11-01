-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_euler__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:16.338373+00:00
-- url     : https://prove2.me/theorems/afd9e5cb-6858-428c-8522-68260024198c
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected graph with the specified crossing-free drawing has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_euler__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    (letI : DecidableRel G.Adj := Classical.decRel _
     ∃ f : ℕ, Fintype.card V + f = G.edgeFinset.card + 2) := by sorry
