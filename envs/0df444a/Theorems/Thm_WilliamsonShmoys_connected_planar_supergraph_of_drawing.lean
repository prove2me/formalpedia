-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_of_drawing
-- name    : WilliamsonShmoys.connected_planar_supergraph_of_drawing
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T02:08:51.439128+00:00
-- url     : https://prove2.me/theorems/ff7c3fa5-c1fe-49b0-9697-eccc1e063958
-- title:
--   Connect components of a planar drawing by added edges
-- statement:
--   Any finite graph with the given crossing-free drawing has a connected planar supergraph on the same vertices. The drawing stays planar as edges are added to join its components. The statement also covers an already connected graph, where no joining edges are needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_supergraph_of_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.Connected := by
  sorry
