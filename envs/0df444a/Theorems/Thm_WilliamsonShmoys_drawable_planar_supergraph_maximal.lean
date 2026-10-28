-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_planar_supergraph_maximal
-- name    : WilliamsonShmoys.drawable_planar_supergraph_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:02:45.724322+00:00
-- url     : https://prove2.me/theorems/653400c2-49e0-4d6c-afc9-91c6c68aac47
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable graph maximal under edge inclusion among drawable graphs on that same vertex type. The claim needs no lower bound on the number of vertices. The source argument is finite maximization over simple graphs; this removes the existence and maximality step from the parent. An independent proof route is to maximize `edgeSet.ncard` over the finite, nonempty set of drawable supergraphs and show that any strict drawable extension would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_planar_supergraph_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ W : SimpleGraph V, HasPlanarDrawingOn W ∧
      (∀ u v, G.Adj u v → W.Adj u v) ∧
      (∀ X : SimpleGraph V, HasPlanarDrawingOn X →
        (∀ u v, W.Adj u v → X.Adj u v) →
        ∀ u v, X.Adj u v → W.Adj u v) := by sorry
