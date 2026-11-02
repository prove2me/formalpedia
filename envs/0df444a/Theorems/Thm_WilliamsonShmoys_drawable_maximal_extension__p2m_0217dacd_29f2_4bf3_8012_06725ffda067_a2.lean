-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_maximal_extension__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a2
-- name    : WilliamsonShmoys.drawable_maximal_extension__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:37:21.327495+00:00
-- url     : https://prove2.me/theorems/5257a613-cd91-4ba5-993c-a40ac10ea2f8
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_maximal_extension__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
