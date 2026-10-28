-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_triangulation_exists_maximal_supergraph
-- name    : WilliamsonShmoys.connected_planar_drawing_triangulation_exists_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:04:47.102503+00:00
-- url     : https://prove2.me/theorems/3ab59c54-3ae0-44d2-a0fa-69a2f47f1d7b
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex type has an inclusion-maximal planar supergraph on the same vertices. Finiteness lets one choose a planar supergraph maximizing its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_triangulation_exists_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
