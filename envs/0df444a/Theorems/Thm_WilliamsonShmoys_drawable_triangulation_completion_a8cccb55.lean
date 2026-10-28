-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_completion_a8cccb55
-- name    : WilliamsonShmoys.drawable_triangulation_completion_a8cccb55
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:14:32.129657+00:00
-- url     : https://prove2.me/theorems/a360d65d-be6d-4f06-9256-c282a404573b
-- title:
--   Triangulated completion of a drawable graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V| − 6 edges. Choose an edge-maximal drawable supergraph, prove it is connected and all faces are triangular by planar edge augmentation, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_triangulation_completion_a8cccb55
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ U : SimpleGraph V,
      W ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
