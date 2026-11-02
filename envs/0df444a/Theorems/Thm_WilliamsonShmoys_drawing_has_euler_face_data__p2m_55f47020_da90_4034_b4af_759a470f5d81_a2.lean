-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawing_has_euler_face_data__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2
-- name    : WilliamsonShmoys.drawing_has_euler_face_data__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:52:19.79126+00:00
-- url     : https://prove2.me/theorems/c696f9c4-5124-4988-8a94-b32da78cbe46
-- title:
--   Extract Euler face data from a planar drawing
-- statement:
--   For the connected graph’s crossing-free drawing, produce a finite face count and a boundary length for each face. The data satisfy Euler’s equation, count each edge twice among face boundaries, and give every facial walk length at least three. The drawing predicate supplies the arcs; a proof must turn them into a plane embedding and establish its facial-walk properties. Connectedness, simplicity, and the vertex lower bound exclude short exceptional walks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawing_has_euler_face_data__p2m_55f47020_da90_4034_b4af_759a470f5d81_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    ∃ (faceCount : Nat) (boundaryLength : Fin faceCount → Nat),
      faceCount + Fintype.card V = G.edgeFinset.card + 2 ∧
      (∑ f : Fin faceCount, boundaryLength f) = 2 * G.edgeFinset.card ∧
      ∀ f, 3 ≤ boundaryLength f := by sorry
