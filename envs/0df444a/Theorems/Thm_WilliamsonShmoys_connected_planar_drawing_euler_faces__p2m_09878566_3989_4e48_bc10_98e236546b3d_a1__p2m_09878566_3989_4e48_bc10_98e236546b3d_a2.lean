-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_faces__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_faces__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:07:34.543879+00:00
-- url     : https://prove2.me/theorems/5d12f344-2925-46a0-8e41-f5b5f2f5ca04
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected graph with the specified crossing-free drawing has a natural face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler_faces__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, f + Fintype.card V = G.edgeSet.ncard + 2 := by
  sorry
