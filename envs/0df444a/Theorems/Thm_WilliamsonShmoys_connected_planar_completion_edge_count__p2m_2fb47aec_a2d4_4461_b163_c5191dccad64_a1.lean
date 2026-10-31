-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_completion_edge_count__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1
-- name    : WilliamsonShmoys.connected_planar_completion_edge_count__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:24.128763+00:00
-- url     : https://prove2.me/theorems/5f0f808e-c07c-4234-8a22-35ebffc68b17
-- title:
--   Connected drawable graphs extend to a triangulation
-- statement:
--   Every connected drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. The independent proof route is to add noncrossing edges until every face is triangular, then use Euler’s formula and face-edge incidence counting. This supplies the completion and exact count; maximality in the parent forces that completion to equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_completion_edge_count__p2m_2fb47aec_a2d4_4461_b163_c5191dccad64_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
