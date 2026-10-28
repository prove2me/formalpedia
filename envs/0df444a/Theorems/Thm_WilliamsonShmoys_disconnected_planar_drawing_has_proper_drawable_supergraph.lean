-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_proper_drawable_supergraph
-- name    : WilliamsonShmoys.disconnected_planar_drawing_has_proper_drawable_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:35:24.738012+00:00
-- url     : https://prove2.me/theorems/f76a5656-9fe3-456c-919d-4433e1731ba3
-- title:
--   A disconnected planar drawing admits a proper drawable supergraph
-- statement:
--   Given a finite linearly ordered vertex type with at least three vertices, any disconnected graph with the specified crossing-free drawing has a drawable supergraph that contains all its edges and at least one additional edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_planar_drawing_has_proper_drawable_supergraph {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hdisc : ¬ H.Connected) : ∃ L : SimpleGraph V, H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ¬ L ≤ H := by sorry
