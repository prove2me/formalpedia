-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
-- name    : WilliamsonShmoys.connected_planar_euler_face_count__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:38:24.623201+00:00
-- url     : https://prove2.me/theorems/26bd9f89-d43e-4d3f-8a04-40a329eaff52
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   For a finite connected graph with the supplied planar drawing, there is a natural face count `f` satisfying Euler’s formula. The connectedness hypothesis is essential: without it, the face count also depends on the number of connected components. A proof route is to extract a finite plane embedding from the drawing and apply Euler’s formula for connected embeddings.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler_face_count__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    ∃ f : ℕ, Fintype.card V + f = N.edgeFinset.card + 2 := by sorry
