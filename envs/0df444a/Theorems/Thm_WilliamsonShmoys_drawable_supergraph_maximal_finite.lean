-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_finite
-- name    : WilliamsonShmoys.drawable_supergraph_maximal_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:31:44.360455+00:00
-- url     : https://prove2.me/theorems/a7270823-000f-4fc0-a886-ab6a2df4cac9
-- title:
--   Maximal drawable supergraph on a finite vertex set
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertex set that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_maximal_finite
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ J : SimpleGraph V,
      G ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V,
        J ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K = J := by sorry
