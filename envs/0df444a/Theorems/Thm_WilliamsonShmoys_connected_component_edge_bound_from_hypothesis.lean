-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_edge_bound_from_hypothesis
-- name    : WilliamsonShmoys.connected_component_edge_bound_from_hypothesis
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:15:26.723265+00:00
-- url     : https://prove2.me/theorems/a7fbf58d-bc74-4eb8-8eb3-7f656450d3a7
-- title:
--   Transfer the bound to a connected component support
-- statement:
--   Transfer the assumed bound to the support of a connected component with at least three vertices. The component support is finite because the ambient vertex type is finite. Turn it into a Finset, apply the hypothesis using connectedness of the component’s induced graph, and identify the finite support cardinality with `C.supp.ncard`. This removes the component-to-induced-subgraph transfer from the aggregation argument. The size cutoff remains exactly three; supports of size less than three are handled separately by the aggregation child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_component_edge_bound_from_hypothesis
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hS : ∀ S : Finset V, 3 ≤ S.card →
      (K.induce (↑S : Set V)).Connected →
      (K.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card)
    (C : K.ConnectedComponent)
    (hC : 3 ≤ C.supp.ncard) :
    (K.induce C.supp).edgeSet.ncard + 6 ≤ 3 * C.supp.ncard := by sorry
