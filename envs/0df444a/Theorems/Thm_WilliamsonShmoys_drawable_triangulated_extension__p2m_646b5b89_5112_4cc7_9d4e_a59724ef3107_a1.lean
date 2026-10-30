-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulated_extension__p2m_646b5b89_5112_4cc7_9d4e_a59724ef3107_a1
-- name    : WilliamsonShmoys.drawable_triangulated_extension__p2m_646b5b89_5112_4cc7_9d4e_a59724ef3107_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:32:05.20199+00:00
-- url     : https://prove2.me/theorems/642d3dbe-c8d0-469e-ba26-5e9db8ed7bc7
-- title:
--   Drawable triangulated supergraph on the same vertices
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_triangulated_extension__p2m_646b5b89_5112_4cc7_9d4e_a59724ef3107_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧
        P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
