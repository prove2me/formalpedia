-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_with_deficient_edge_count_has_proper_drawable_extension_b5197173
-- name    : WilliamsonShmoys.drawable_graph_with_deficient_edge_count_has_proper_drawable_extension_b5197173
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:34:49.671506+00:00
-- url     : https://prove2.me/theorems/be664796-cf08-43bf-a690-72284ce2f02d
-- title:
--   Drawable extension below the planar edge bound
-- statement:
--   A drawable simple graph on at least three vertices with fewer than 3n - 6 edges has a strict drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_with_deficient_edge_count_has_proper_drawable_extension_b5197173
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcount : M.edgeSet.ncard < 3 * Fintype.card V - 6) :
    Exists (fun N : SimpleGraph V =>
      And (M <= N)
        (And (Not (N = M)) (WilliamsonShmoys.HasPlanarDrawingOn N))) := by sorry
