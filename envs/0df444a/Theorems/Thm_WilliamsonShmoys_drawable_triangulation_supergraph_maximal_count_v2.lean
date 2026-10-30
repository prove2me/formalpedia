-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_supergraph_maximal_count_v2
-- name    : WilliamsonShmoys.drawable_triangulation_supergraph_maximal_count_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:31:10.236968+00:00
-- url     : https://prove2.me/theorems/84313d63-20c1-4b06-bed6-810239f90b6b
-- title:
--   Edge count of a maximum drawable supergraph
-- statement:
--   A drawable graph with at least three vertices that maximizes edge count among its drawable supergraphs on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_triangulation_supergraph_maximal_count_v2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hdraw : HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M.edgeSet.ncard ≤ L.edgeSet.ncard) : 3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
