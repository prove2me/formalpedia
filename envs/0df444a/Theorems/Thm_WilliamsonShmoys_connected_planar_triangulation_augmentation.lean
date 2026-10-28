-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_triangulation_augmentation
-- name    : WilliamsonShmoys.connected_planar_triangulation_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:03:36.780686+00:00
-- url     : https://prove2.me/theorems/d6c1cda6-0c6b-4181-879b-1515d91138b3
-- title:
--   Augment a connected planar graph to a triangulation
-- statement:
--   Every connected simple graph on at least three vertices with a crossing-free drawing can be augmented, without changing its vertex type, to a drawn planar supergraph whose edge count is exactly three times the number of vertices minus six. The explicit edge-count monotonicity conjunct supports the parent’s short arithmetic derivation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_triangulation_augmentation
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
