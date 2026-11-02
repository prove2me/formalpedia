-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_certificate__p2m_b5c387cc_fe7e_4039_9011_ee95aed75dd4_a2
-- name    : WilliamsonShmoys.connected_planar_euler_face_certificate__p2m_b5c387cc_fe7e_4039_9011_ee95aed75dd4_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:57:22.183192+00:00
-- url     : https://prove2.me/theorems/034f5ef2-6768-4eb9-83c3-8c1c8d5ce02b
-- title:
--   Euler and face-incidence certificate for a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and the supplied crossing-free drawing, there is a natural face count satisfying Euler’s equation and the lower bound of three edge-side incidences per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_euler_face_certificate__p2m_b5c387cc_fe7e_4039_9011_ee95aed75dd4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * H.edgeFinset.card := by sorry
