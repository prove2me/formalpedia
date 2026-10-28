-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_cardinal_max_7f31c9a2
-- name    : WilliamsonShmoys.drawable_supergraph_cardinal_max_7f31c9a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:21:54.154053+00:00
-- url     : https://prove2.me/theorems/0a7cda2a-beac-4d35-9eeb-98245b7504f1
-- title:
--   Maximum edge count among drawable supergraphs
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set whose edge count is at least that of every drawable supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_cardinal_max_7f31c9a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V,
        K.edgeSet ⊆ H.edgeSet →
        HasPlanarDrawingOn H →
        H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
