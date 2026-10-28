-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_aea3a4e2
-- name    : WilliamsonShmoys.drawable_supergraph_maximal_aea3a4e2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:06:04.691386+00:00
-- url     : https://prove2.me/theorems/cf1b2821-a114-481c-9af9-35dec7e6121d
-- title:
--   Maximal drawable supergraph on the same vertex type
-- statement:
--   Every drawable finite graph has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_supergraph_maximal_aea3a4e2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      Set.Subset H.edgeSet K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, Set.Subset K.edgeSet L.edgeSet →
        HasPlanarDrawingOn L → Set.Subset L.edgeSet K.edgeSet) := by sorry
