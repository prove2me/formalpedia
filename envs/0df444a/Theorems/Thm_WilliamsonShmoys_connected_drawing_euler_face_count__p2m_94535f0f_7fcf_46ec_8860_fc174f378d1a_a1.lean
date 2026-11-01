-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_count__p2m_94535f0f_7fcf_46ec_8860_fc174f378d1a_a1
-- name    : WilliamsonShmoys.connected_drawing_euler_face_count__p2m_94535f0f_7fcf_46ec_8860_fc174f378d1a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:57:29.403768+00:00
-- url     : https://prove2.me/theorems/09878566-3989-4e48-bc10-98e236546b3d
-- title:
--   Euler face count and incidence bound for a connected planar drawing
-- statement:
--   For a connected simple graph on at least three vertices with the specified crossing-free drawing, there is a natural number of faces satisfying Euler’s formula and the lower bound on total face-boundary incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_drawing_euler_face_count__p2m_94535f0f_7fcf_46ec_8860_fc174f378d1a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ,
      f + Fintype.card V = G.edgeSet.ncard + 2 ∧
      3 * f <= 2 * G.edgeSet.ncard := by
  sorry
