-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_count_lower_bound
-- name    : WilliamsonShmoys.drawable_supergraph_edge_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:31:34.879928+00:00
-- url     : https://prove2.me/theorems/6806e764-8684-4246-93b2-a7ef08b08a0a
-- title:
--   Drawable graph augmentation to the planar edge lower bound
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same finite vertex type with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ P : SimpleGraph V, G ≤ P ∧ HasPlanarDrawingOn P ∧
      3 * (Fintype.card V : Int) - 6 ≤ (P.edgeSet.ncard : Int) := by sorry
