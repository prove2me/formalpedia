-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1
-- name    : WilliamsonShmoys_connected_planar_euler_face_count__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:49:18.226107+00:00
-- url     : https://prove2.me/theorems/8ea79346-1dcf-4327-beb0-f05cd39c169c
-- title:
--   Euler face count for a connected drawn graph
-- statement:
--   A finite connected graph with the specified plane drawing has a face count f satisfying f + |V| = |E| + 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys_connected_planar_euler_face_count__p2m_ebe2fe48_3b22_4672_8ecb_0d78f061f679_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hConnected : G.Connected) :
    ∃ f : ℕ, f + Fintype.card V = G.edgeSet.ncard + 2 := by sorry
