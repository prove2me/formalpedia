-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_induced_edge_ncard_sum
-- name    : WilliamsonShmoys.component_induced_edge_ncard_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:38:40.514425+00:00
-- url     : https://prove2.me/theorems/f27d8268-ff31-4b0b-b0f4-a273ec9adaa1
-- title:
--   Component-induced edge sets partition the edges
-- statement:
--   The sum of the induced edge counts over component supports is the total edge count. Every edge’s endpoints belong to the same connected component, so each edge occurs in exactly one of these induced edge sets. This removes the edge-count identification from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.component_induced_edge_ncard_sum
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) :
    (∑ C : K.ConnectedComponent, (K.induce C.supp).edgeSet.ncard) =
      K.edgeSet.ncard := by sorry
