-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_count_aggregation_induced_edge_count_sum_edge_equiv_sigma
-- name    : WilliamsonShmoys.component_edge_count_aggregation_induced_edge_count_sum.edge_equiv_sigma
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:03:43.115458+00:00
-- url     : https://prove2.me/theorems/73b692f2-cb0f-4908-9c91-2854246a72bc
-- title:
--   Global edges correspond to induced edges of their unique parts
-- statement:
--   There is a bijection between global graph edges and pairs consisting of a part and an edge in the graph induced by that part. The common part is unique because each endpoint belongs to exactly one part.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open scoped Classical

theorem WilliamsonShmoys.component_edge_count_aggregation_induced_edge_count_sum.edge_equiv_sigma
    {V : Type} [Fintype V] (H : SimpleGraph V) (C : Finset (Finset V))
    (hPartition : (∀ S ∈ C, S.Nonempty) ∧
      ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S)
    (hNoCross : ∀ ⦃u v : V⦄, H.Adj u v →
      ∃ S ∈ C, u ∈ S ∧ v ∈ S) :
    Nonempty (H.edgeSet ≃
      Σ S : C, {e : Sym2 (↑(S : Finset V)) //
        e ∈ (H.induce (↑(S : Finset V) : Set V)).edgeSet}) := by sorry
