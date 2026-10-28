-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_drawing_has_maximal_supergraph
-- name    : WilliamsonShmoys.disconnected_drawing_has_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:00:30.630168+00:00
-- url     : https://prove2.me/theorems/ed38fd6e-6346-4f72-944a-b00efa3f43ce
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that is maximal among drawable supergraphs on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_drawing_has_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V,
        J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J := by sorry
