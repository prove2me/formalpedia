-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_completion
-- name    : WilliamsonShmoys.drawable_graph_has_triangulating_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:58:00.891445+00:00
-- url     : https://prove2.me/theorems/399d67b6-1225-43ef-9a0c-578821b9bf96
-- title:
--   Drawable graph triangulating completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. Maximality in the parent forces this completion to have the same edge set as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_triangulating_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
