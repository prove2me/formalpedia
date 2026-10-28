-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_can_be_extended
-- name    : WilliamsonShmoys.drawable_graph_can_be_extended
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:11:35.716152+00:00
-- url     : https://prove2.me/theorems/df7dfb14-d1bb-4ec9-be14-2c7e4b30e5b4
-- title:
--   Strictly short planar graphs admit an edge extension
-- statement:
--   If a drawable simple graph on at least three vertices is strictly below the planar edge bound, it has a drawable proper supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_can_be_extended
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hshort : G.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧ L ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
