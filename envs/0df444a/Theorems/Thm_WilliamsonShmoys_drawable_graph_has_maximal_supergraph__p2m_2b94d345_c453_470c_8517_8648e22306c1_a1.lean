-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_supergraph__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_supergraph__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:24:26.633982+00:00
-- url     : https://prove2.me/theorems/71046448-d1b2-48c5-9046-e21fa2ecd00c
-- title:
--   Every drawable graph has a maximal drawable supergraph
-- statement:
--   Any graph with a drawing has a drawable supergraph on the same finite vertex type that has no strict drawable supergraph. Since the collection of graphs on a finite vertex type is finite and contains H, choose a drawable supergraph maximal under inclusion. This applies to disconnected graphs and requires no assumption that the vertex set is nonempty. The child removes the finite maximal-choice step from the parent; its independent proof route is finite maximization among drawable supergraphs. The remaining work is establishing the maximal graph’s edge count in the second child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_maximal_supergraph__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ L : SimpleGraph V, H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ K : SimpleGraph V, L ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ L := by sorry
