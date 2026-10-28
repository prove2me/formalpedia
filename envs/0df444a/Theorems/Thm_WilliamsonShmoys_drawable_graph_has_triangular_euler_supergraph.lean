-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangular_euler_supergraph
-- name    : WilliamsonShmoys.drawable_graph_has_triangular_euler_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:16:19.504991+00:00
-- url     : https://prove2.me/theorems/d1fe8e84-e753-46d3-ad1d-3fec068e3440
-- title:
--   A drawable graph has a triangular Euler certificate in a drawable supergraph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edges and triangular faces satisfy the Euler certificate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularEulerCertificate

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangular_euler_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ X : SimpleGraph V,
      U ≤ X ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      WilliamsonShmoys.HasTriangularEulerCertificate X := by
  sorry
