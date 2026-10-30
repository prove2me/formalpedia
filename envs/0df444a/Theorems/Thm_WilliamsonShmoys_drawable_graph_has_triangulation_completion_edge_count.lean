-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulation_completion_edge_count
-- name    : WilliamsonShmoys.drawable_graph_has_triangulation_completion_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:43:07.223563+00:00
-- url     : https://prove2.me/theorems/95127aba-aeee-40a3-90fc-90ced95f742a
-- title:
--   Triangulation completion edge count
-- statement:
--   Every graph with a crossing-free drawing and at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. The lower bound includes the three-vertex case, where the completion is the triangle. The child packages the topological augmentation and Euler-counting step; a proof route is to add noncrossing edges within faces until the embedding is triangulated, then count face-edge incidences using Euler’s formula. This is a substantial new argument for the given drawing predicate; the available local files do not contain a formal proof to port.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulation_completion_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V) :
    ∃ U : SimpleGraph V,
      (∀ {u v}, T.Adj u v → U.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
