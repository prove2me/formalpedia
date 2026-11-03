-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
-- name    : WilliamsonShmoys.connected_planar_drawing_euler__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:02:42.486159+00:00
-- url     : https://prove2.me/theorems/e2c3d283-ca92-493d-91bc-6ba22f4f1ed2
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with a crossing-free drawing has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeFinset.card + 2 := by
  sorry
