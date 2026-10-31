-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_faces__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_faces__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:52:15.235818+00:00
-- url     : https://prove2.me/theorems/8f73fa75-8815-41ab-9263-4c27c806efcb
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected finite graph with the supplied planar drawing has a natural face count satisfying Euler’s formula, |V| + f = |E| + 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_euler_faces__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
