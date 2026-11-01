-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_certificate__p2m_792d8105_156d_4ec7_b9fb_1feb01e02200_a1
-- name    : WilliamsonShmoys.connected_planar_euler_face_certificate__p2m_792d8105_156d_4ec7_b9fb_1feb01e02200_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:10.509449+00:00
-- url     : https://prove2.me/theorems/5594ab01-5507-4608-93d6-8bce1469fe90
-- title:
--   Euler face and incidence certificate for a connected planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, there is a natural number of faces f such that Euler’s relation holds and the total face-boundary incidence count is at least three per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_euler_face_certificate__p2m_792d8105_156d_4ec7_b9fb_1feb01e02200_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * H.edgeFinset.card := by sorry
