-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_extension_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
-- name    : WilliamsonShmoys.drawable_supergraph_maximal_extension_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:30:42.506651+00:00
-- url     : https://prove2.me/theorems/a4953c12-9d36-46b3-a2a7-401b5e7f6eb3
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among its drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_maximal_extension_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hXdraw : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V, X ≤ Y ∧
      WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      ∀ Z : SimpleGraph V, Y ≤ Z →
        WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y := by sorry
