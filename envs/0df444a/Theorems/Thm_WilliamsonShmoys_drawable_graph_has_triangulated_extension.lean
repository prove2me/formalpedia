-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_extension
-- name    : WilliamsonShmoys.drawable_graph_has_triangulated_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:25:40.388642+00:00
-- url     : https://prove2.me/theorems/792d6233-0413-48c2-8c4d-fb4d15268d51
-- title:
--   Extend a drawable graph to a triangulation
-- statement:
--   Any finite drawable graph with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3|V|−6. The intended independent proof is to extend the drawing by adding noncrossing edges through faces until it is triangulated, then use Euler's formula and face-edge incidence counting. The size hypothesis rules out the small-vertex exceptions; formalizing face augmentation for the given continuous-arc predicate is the core work removed from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulated_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hWdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hCard : 3 <= Fintype.card V) :
    ∃ X : SimpleGraph V,
      W <= X ∧ WilliamsonShmoys.HasPlanarDrawingOn X ∧
        3 * Fintype.card V = X.edgeSet.ncard + 6 := by sorry
