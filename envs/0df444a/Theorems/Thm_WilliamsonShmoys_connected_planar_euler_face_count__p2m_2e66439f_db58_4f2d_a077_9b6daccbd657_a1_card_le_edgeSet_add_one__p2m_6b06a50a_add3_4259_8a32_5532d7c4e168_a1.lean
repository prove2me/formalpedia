-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1_card_le_edgeSet_add_one__p2m_6b06a50a_add3_4259_8a32_5532d7c4e168_a1
-- name    : WilliamsonShmoys.connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1_card_le_edgeSet_add_one__p2m_6b06a50a_add3_4259_8a32_5532d7c4e168_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:49:44.422145+00:00
-- url     : https://prove2.me/theorems/cfc34fc8-40be-4b7b-9114-891e51f1fd2c
-- title:
--   A finite connected graph has at least one fewer edge than vertices
-- statement:
--   For a finite connected simple graph, the number of vertices is at most the number of edges plus one. A spanning tree proves this bound; the drawing hypothesis is not needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler_face_count__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1_card_le_edgeSet_add_one__p2m_6b06a50a_add3_4259_8a32_5532d7c4e168_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hConnected : G.Connected) : Fintype.card V ≤ G.edgeSet.ncard + 1 := by sorry
