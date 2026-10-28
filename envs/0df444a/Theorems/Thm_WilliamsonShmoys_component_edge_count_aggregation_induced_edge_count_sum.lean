-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_count_aggregation_induced_edge_count_sum
-- name    : WilliamsonShmoys.component_edge_count_aggregation_induced_edge_count_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:28:07.364419+00:00
-- url     : https://prove2.me/theorems/5cec665e-4501-4db1-a705-c20d3f797ab7
-- title:
--   Global edge count is the sum of induced edge counts
-- statement:
--   When the parts partition the vertices and every edge has both endpoints in a part, each global edge is counted in exactly one induced subgraph, so the global edge count equals the sum of the induced edge counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.component_edge_count_aggregation_induced_edge_count_sum
    (V : Type) [Fintype V]
    (H : SimpleGraph V)
    (C : Finset (Finset V))
    (hPartition : (∀ S ∈ C, S.Nonempty) ∧
      ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S)
    (hNoCross : ∀ ⦃u v : V⦄, H.Adj u v →
      ∃ S ∈ C, u ∈ S ∧ v ∈ S) :
    H.edgeSet.ncard =
      C.sum (fun S => (H.induce (↑S : Set V)).edgeSet.ncard) := by sorry
