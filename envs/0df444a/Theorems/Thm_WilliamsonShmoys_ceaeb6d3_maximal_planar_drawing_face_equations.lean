-- Prove2me | Theorems.Thm_WilliamsonShmoys_ceaeb6d3_maximal_planar_drawing_face_equations
-- name    : WilliamsonShmoys.ceaeb6d3_maximal_planar_drawing_face_equations
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T15:31:40.233989+00:00
-- url     : https://prove2.me/theorems/53625c57-a16b-47f3-a6ce-b851d1240508
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   For a drawable graph with at least three vertices that is maximal among drawable supergraphs on that vertex type, there is a natural-number face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.ceaeb6d3_maximal_planar_drawing_face_equations
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
