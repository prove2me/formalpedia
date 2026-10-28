-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_count_aggregation
-- name    : WilliamsonShmoys.component_edge_count_aggregation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:26:41.134687+00:00
-- url     : https://prove2.me/theorems/1bae8de1-62dc-4335-a1d0-503925202f58
-- title:
--   Aggregate edge bounds across a component partition
-- statement:
--   Given a finite nonempty vertex partition in which every edge lies inside one part, sum the local induced-subgraph edge bounds to obtain the global planar bound. Uniqueness of each vertex’s part and the no-cross-edge hypothesis ensure that each edge is counted in exactly one induced component. If there is a component of size at least three, its `−6` allowance and the vertex-count contribution from the remaining parts absorb their local edge counts. If all parts have size at most two, their edges total at most half the vertex count, which is at most `3|V|−6` for `|V|≥3`. This is a graph-counting lemma independent of planarity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.component_edge_count_aggregation
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (C : Finset (Finset V))
    (hPartition : (∀ S ∈ C, S.Nonempty) ∧
      ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S)
    (hNoCross : ∀ ⦃u v : V⦄, H.Adj u v →
      ∃ S ∈ C, u ∈ S ∧ v ∈ S)
    (hLocal : ∀ S ∈ C,
      (H.induce (↑S : Set V)).edgeSet.ncard ≤
        (if S.card < 3 then S.card / 2 else 3 * S.card - 6))
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
