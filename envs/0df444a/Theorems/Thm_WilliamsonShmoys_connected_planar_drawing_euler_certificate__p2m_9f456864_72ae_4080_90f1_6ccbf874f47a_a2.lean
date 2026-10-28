-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_certificate__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_certificate__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:09:01.131701+00:00
-- url     : https://prove2.me/theorems/bddb7bfa-7c36-4521-ae23-809461c66ee9
-- title:
--   Euler certificate for a connected planar drawing
-- statement:
--   For a connected finite simple graph with at least three vertices and the supplied crossing-free drawing, produce a face count satisfying Euler’s equation and the face-boundary inequality. The concrete route is to obtain the plane embedding from the arcs, apply Euler’s formula, and count the two sides of each edge; simplicity and the vertex lower bound ensure each face boundary has length at least three. This isolates the central planar topology and counting argument. The hypotheses exclude the small connected graphs where the face-boundary inequality can fail.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_euler_certificate__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
