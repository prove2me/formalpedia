-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_extension_maximal_for_edge_count
-- name    : WilliamsonShmoys.drawable_extension_maximal_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:38:42.950882+00:00
-- url     : https://prove2.me/theorems/45f8dd95-6605-4ca8-b365-e00bbc8b4e9d
-- title:
--   A drawable graph has an inclusion-maximal drawable extension
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type has a drawable supergraph on that same type that is maximal under inclusion among drawable supergraphs. This removes only the finite selection step; it leaves the sharp edge-count theorem to the second child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_extension_maximal_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ U : SimpleGraph V, G ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      ∀ H : SimpleGraph V, U ≤ H →
        WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ U := by sorry
