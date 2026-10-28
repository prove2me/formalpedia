-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_planar_extension
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_planar_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:57:59.794924+00:00
-- url     : https://prove2.me/theorems/b078dc42-359a-4e13-bb74-c481f20f61dd
-- title:
--   Every drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that admits no strictly larger drawable supergraph on that type. Since there are only finitely many simple graphs on the vertex type, choose a drawable supergraph with maximal edge count; any drawable extension must then have the same edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_maximal_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ Z : SimpleGraph V, G ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      ∀ W : SimpleGraph V, Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z := by sorry
