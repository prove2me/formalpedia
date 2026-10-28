-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_disconnected_edge_extension
-- name    : WilliamsonShmoys.drawable_disconnected_edge_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:49:34.018991+00:00
-- url     : https://prove2.me/theorems/4c640fcb-ce6c-4b86-a4a4-d74d3ee34be1
-- title:
--   A disconnected drawable graph with at least three vertices admits a drawable edge extension
-- statement:
--   Every disconnected drawable simple graph on at least three vertices has a drawable supergraph containing an edge absent from the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_disconnected_edge_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V)
    (hdisc : ¬ Q.Connected) :
    ∃ M : SimpleGraph V,
      Q ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∃ u v, M.Adj u v ∧ ¬ Q.Adj u v := by sorry
