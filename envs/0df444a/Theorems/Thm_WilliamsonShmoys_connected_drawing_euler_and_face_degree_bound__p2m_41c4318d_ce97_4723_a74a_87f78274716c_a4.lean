-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_and_face_degree_bound__p2m_41c4318d_ce97_4723_a74a_87f78274716c_a4
-- name    : WilliamsonShmoys.connected_drawing_euler_and_face_degree_bound__p2m_41c4318d_ce97_4723_a74a_87f78274716c_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T05:13:08.88299+00:00
-- url     : https://prove2.me/theorems/74636254-a954-4b01-9b70-979bcb3da8e1
-- title:
--   Euler and face-degree bounds for a connected drawing
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, there is a natural number of faces satisfying Euler's formula, with total face degree at least three per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_drawing_euler_and_face_degree_bound__p2m_41c4318d_ce97_4723_a74a_87f78274716c_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = G.edgeSet.ncard + 2 /\
      3 * f <= 2 * G.edgeSet.ncard := by sorry
