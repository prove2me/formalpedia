-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_face_data__p2m_93e8e51b_b659_4e57_adae_24ec3eefdfaa_a2
-- name    : WilliamsonShmoys.connected_planar_face_data__p2m_93e8e51b_b659_4e57_adae_24ec3eefdfaa_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:34:53.524671+00:00
-- url     : https://prove2.me/theorems/bc066f5c-1421-450b-9266-8103a5957640
-- title:
--   Finite face-boundary data for a connected planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has finitely many face-boundary lengths satisfying Euler’s formula, summing to twice the number of edges, with every length at least three. Bridge edges count twice in the boundary total.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_face_data__p2m_93e8e51b_b659_4e57_adae_24ec3eefdfaa_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ k : ℕ, ∃ boundary : Fin k → ℕ,
      Fintype.card V + k = H.edgeSet.ncard + 2 ∧
      (∑ i, boundary i) = 2 * H.edgeSet.ncard ∧
      ∀ i, 3 ≤ boundary i := by sorry
