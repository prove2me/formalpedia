-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_of_drawing_of_card_ge_three
-- name    : WilliamsonShmoys.connected_planar_supergraph_of_drawing_of_card_ge_three
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:25:07.78409+00:00
-- url     : https://prove2.me/theorems/b64379a3-1a0d-4479-a3ba-0e5902120ace
-- title:
--   Connect a planar drawing when there are at least three vertices
-- statement:
--   Given the target's lower bound of at least three vertices, extend the planar drawing by edges to a connected planar graph on the same vertex type. The added edges join distinct components while preserving the drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_supergraph_of_drawing_of_card_ge_three
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.Connected := by
  sorry
