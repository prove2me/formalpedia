-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawingOn_restrict_induce_282b0fbb
-- name    : WilliamsonShmoys.drawingOn_restrict_induce_282b0fbb
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:11:21.281594+00:00
-- url     : https://prove2.me/theorems/3656f4e0-7c56-49fb-82c6-dce6b7b3fd9a
-- title:
--   Restrict a planar drawing to an induced subgraph
-- statement:
--   Restricting the vertex placement and edge arcs of a drawing to a finite vertex subset gives a drawing for the induced subgraph. The proof restricts the witnessing functions and inherits injectivity, continuity, endpoint, and nonintersection properties.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.drawingOn_restrict_induce_282b0fbb
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (S : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (L.induce S) := by sorry
