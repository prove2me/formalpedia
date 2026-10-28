-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_fe39cb94_f82e_4553_8662_9097c26d5d3d
-- name    : WilliamsonShmoys.drawable_supergraph_maximal_fe39cb94_f82e_4553_8662_9097c26d5d3d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:48:20.546099+00:00
-- url     : https://prove2.me/theorems/b18e5495-f367-4271-9736-9621d8d934c0
-- title:
--   A maximal drawable supergraph exists
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph maximal under edge inclusion. The finite maximization argument needs no lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_supergraph_maximal_fe39cb94_f82e_4553_8662_9097c26d5d3d
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L) := by sorry
