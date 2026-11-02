-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_has_euler_face_data__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2_euler_and_incidence__p2m_c696f9c4_5124_4988_8a94_b32da78cbe46_a1
-- name    : WilliamsonShmoys.drawing_has_euler_face_data__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2_euler_and_incidence__p2m_c696f9c4_5124_4988_8a94_b32da78cbe46_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:58:11.077321+00:00
-- url     : https://prove2.me/theorems/0caaf1a5-9fd2-4503-b696-0441c7443d96
-- title:
--   Euler equation and edge incidence for drawing-derived face data
-- statement:
--   Construct a finite set of faces and a natural-number boundary length for each, with Euler’s equation and total boundary length twice the number of edges. This removes the global topological counting and edge-incidence obligations from the parent while leaving short-face exclusion for the other child. A proof route is to derive a plane embedding from the explicit crossing-free arcs, then use the Euler characteristic of the plane and count each edge on its two sides. The face construction and those counting arguments remain substantial formalization work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawing_has_euler_face_data__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2_euler_and_incidence__p2m_c696f9c4_5124_4988_8a94_b32da78cbe46_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    ∃ (faceCount : Nat) (boundaryLength : Fin faceCount → Nat),
      faceCount + Fintype.card V = G.edgeFinset.card + 2 ∧
      (∑ f : Fin faceCount, boundaryLength f) = 2 * G.edgeFinset.card := by sorry
