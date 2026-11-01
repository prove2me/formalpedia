-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_supergraph__p2m_694a8160_ff76_4855_a03b_16e16dbb37d5_a1
-- name    : WilliamsonShmoys.drawable_graph_has_triangulated_supergraph__p2m_694a8160_ff76_4855_a03b_16e16dbb37d5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:23:24.070973+00:00
-- url     : https://prove2.me/theorems/bc038eff-dd8d-4b01-9048-8ba39788938c
-- title:
--   Extend a drawable graph to a triangulation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. The inclusion condition preserves every existing edge; the lemma does not require the original graph to be connected or maximal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulated_supergraph__p2m_694a8160_ff76_4855_a03b_16e16dbb37d5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    exists L : SimpleGraph V,
      (forall {u v : V}, K.Adj u v -> L.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj
       L.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
