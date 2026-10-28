-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_face_count_bounds
-- name    : WilliamsonShmoys.connected_drawing_face_count_bounds
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:18:19.414404+00:00
-- url     : https://prove2.me/theorems/eae47bd5-7de5-4008-8b4d-905caace217a
-- title:
--   Euler and face-boundary counts for a connected drawing
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, there is a natural number of faces f such that Euler’s formula holds and the sum of facial boundary lengths gives 3f ≤ 2|E|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_drawing_face_count_bounds
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by sorry
