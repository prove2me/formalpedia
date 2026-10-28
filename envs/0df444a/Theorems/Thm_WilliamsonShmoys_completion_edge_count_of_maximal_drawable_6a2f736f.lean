-- Prove2me | Theorems.Thm_WilliamsonShmoys_completion_edge_count_of_maximal_drawable_6a2f736f
-- name    : WilliamsonShmoys.completion_edge_count_of_maximal_drawable_6a2f736f
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:27:29.486995+00:00
-- url     : https://prove2.me/theorems/aad9569e-3b02-4b25-a2de-035820e22467
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal graph admitting the stated plane drawing, with at least three vertices, has exactly 3n−6 edges. The proof must derive connectedness and triangular faces from maximality and the drawing conditions, then use Euler’s formula; it must cover the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.completion_edge_count_of_maximal_drawable_6a2f736f
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ¬ ∃ H : SimpleGraph V,
      K < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
