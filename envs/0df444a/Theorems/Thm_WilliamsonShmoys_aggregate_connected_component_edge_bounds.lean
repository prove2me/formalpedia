-- Prove2me | Theorems.Thm_WilliamsonShmoys_aggregate_connected_component_edge_bounds
-- name    : WilliamsonShmoys.aggregate_connected_component_edge_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:19:20.553522+00:00
-- url     : https://prove2.me/theorems/bd236f16-e7f7-4063-8b2b-5352c9878d36
-- title:
--   Aggregate edge bounds over connected components
-- statement:
--   Aggregate component-support bounds to obtain the whole-graph bound. Partition vertices and edges by connected component, apply the supplied bound to supports of size at least three, and use simplicity to bound the edge counts of singleton and two-vertex supports. A large component already contributes a deficit of at least six; if all components are small, the total vertex-count hypothesis ensures their combined deficits are at least six. This is the finite bookkeeping step needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.aggregate_connected_component_edge_bounds
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hC : ∀ C : K.ConnectedComponent,
      3 ≤ C.supp.ncard →
      (K.induce C.supp).edgeSet.ncard + 6 ≤ 3 * C.supp.ncard) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
