-- Prove2me | Theorems.Thm_WilliamsonShmoys_connectedComponent_edge_conservation_disjoint__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a2
-- name    : WilliamsonShmoys.connectedComponent_edge_conservation_disjoint__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:55:00.090518+00:00
-- url     : https://prove2.me/theorems/9c944e48-3248-4b41-826f-8af0b6f3bcab
-- title:
--   Edges are conserved across disjoint partition blocks
-- statement:
--   For a finite simple graph, if the vertex blocks are pairwise disjoint and every edge has both endpoints in some block, then the sum of the induced-subgraph edge counts equals the graph’s edge count. Disjointness ensures that no edge is counted in more than one block.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.connectedComponent_edge_conservation_disjoint__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (C : Finset (Finset V))
    (hdisj : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t)
    (hpair : ∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    (letI : DecidableRel L.Adj := dL;
    (∑ s ∈ C, (L.induce (↑s : Set V)).edgeFinset.card) = L.edgeFinset.card) := by sorry
