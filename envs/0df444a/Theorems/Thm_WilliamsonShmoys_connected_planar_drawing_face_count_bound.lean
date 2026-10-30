-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_count_bound
-- name    : WilliamsonShmoys.connected_planar_drawing_face_count_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:58:01.401596+00:00
-- url     : https://prove2.me/theorems/80d85d81-880e-495e-8674-df20fe1a4c17
-- title:
--   Euler face count and minimum boundary length for a connected planar drawing
-- statement:
--   For a finite simple graph with at least three vertices and a connected crossing-free drawing, there is a natural number of faces f such that Euler’s relation holds and three times the number of faces is at most twice the number of edges. The latter bound records that every face-boundary walk has length at least three while every edge contributes two sides in total.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_face_count_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      G.edgeSet.ncard + 2 = Fintype.card V + f ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
