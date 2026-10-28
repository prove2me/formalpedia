-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_dense_supergraph
-- name    : WilliamsonShmoys.drawable_graph_has_dense_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:53:17.090996+00:00
-- url     : https://prove2.me/theorems/4abbea4b-d91a-40b0-b03f-739e009c940e
-- title:
--   A drawable graph has a dense drawable supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.drawable_graph_has_dense_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ P : SimpleGraph V, M ≤ P ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by sorry
