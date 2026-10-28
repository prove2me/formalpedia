-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_edge_maximal_completion
-- name    : WilliamsonShmoys.drawable_graph_has_edge_maximal_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:50:54.360505+00:00
-- url     : https://prove2.me/theorems/8c134cc0-a9c8-428e-9792-186585ec2868
-- title:
--   Edge-maximal drawable completion
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under drawable edge additions. This is consistent at the three-vertex boundary: the original graph can be extended to a triangle. A proof route is to maximize edge count among the finite set of simple graphs on V that contain T and admit the given kind of drawing. Any proper drawable supergraph would have more edges and contradict maximality. This removes the completion and maximality step from the parent; the topological representation of the drawing predicate and the finite maximization argument remain to be formalized.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_edge_maximal_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V) :
    ∃ U : SimpleGraph V,
      (∀ {u v}, T.Adj u v → U.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      (∀ W : SimpleGraph V,
        (∀ {u v}, U.Adj u v → W.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn W → W = U) := by sorry
