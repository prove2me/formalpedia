-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound_finite_maximal_extension
-- name    : WilliamsonShmoys.connected_planar_edge_upper_bound_finite_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:17:16.119728+00:00
-- url     : https://prove2.me/theorems/8083b65b-0640-4ed5-be9d-fa6a6b3c4ab2
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every finite graph with the specified planar drawing is contained in a planar supergraph on the same vertex type that is maximal among planar supergraphs; its edge count is at least that of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_upper_bound_finite_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ K' : SimpleGraph V, K ≤ K' →
        WilliamsonShmoys.HasPlanarDrawingOn K' → K' = K) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
