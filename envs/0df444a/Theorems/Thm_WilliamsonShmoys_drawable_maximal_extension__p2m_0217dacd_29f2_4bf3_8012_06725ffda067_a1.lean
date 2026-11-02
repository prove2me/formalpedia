-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_maximal_extension__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a1
-- name    : WilliamsonShmoys.drawable_maximal_extension__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:23:17.068196+00:00
-- url     : https://prove2.me/theorems/3b2acd1e-2b32-465b-803a-e7344ffe262c
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex type has a planar supergraph on the same vertices that admits no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_maximal_extension__p2m_0217dacd_29f2_4bf3_8012_06725ffda067_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
