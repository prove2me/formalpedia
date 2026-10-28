-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_with_maximal_planar_edge_count
-- name    : WilliamsonShmoys.drawable_supergraph_with_maximal_planar_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:52:39.840397+00:00
-- url     : https://prove2.me/theorems/e096120b-1504-4385-8926-9c9b31182dea
-- title:
--   Triangulated planar extension on the same vertices
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This packages the planar extension-to-triangulation argument and Euler count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_supergraph_with_maximal_planar_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
