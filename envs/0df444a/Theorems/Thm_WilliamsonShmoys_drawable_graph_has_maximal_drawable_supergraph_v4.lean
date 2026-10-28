-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_drawable_supergraph_v4
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph_v4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:18:25.411217+00:00
-- url     : https://prove2.me/theorems/9410c0b1-6ff6-44fc-ab43-c62913e56c8f
-- title:
--   Every drawable finite graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph that has no strictly larger drawable supergraph on the same vertices. This follows by maximizing the edge set among the finitely many supergraphs of L that have a planar drawing; L itself ensures the collection is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph_v4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by sorry
