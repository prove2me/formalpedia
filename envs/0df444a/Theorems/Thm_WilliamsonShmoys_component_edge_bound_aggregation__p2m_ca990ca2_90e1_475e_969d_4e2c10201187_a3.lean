-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_bound_aggregation__p2m_ca990ca2_90e1_475e_969d_4e2c10201187_a3
-- name    : WilliamsonShmoys.component_edge_bound_aggregation__p2m_ca990ca2_90e1_475e_969d_4e2c10201187_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:13:22.765966+00:00
-- url     : https://prove2.me/theorems/4ae72016-0cf1-4754-9ecd-3561950d201b
-- title:
--   Aggregate connected-component edge bounds
-- statement:
--   If every connected induced subgraph on at least three vertices satisfies the planar edge bound, then the whole finite graph with at least three vertices satisfies it. Partition into connected components, apply the local bound to larger components, bound components of size one or two directly, and sum. The remaining core obligation is the finite component partition and edge-count aggregation in Lean.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys.component_edge_bound_aggregation__p2m_ca990ca2_90e1_475e_969d_4e2c10201187_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hLocal : ∀ (s : Finset V), 3 ≤ s.card →
      (L.induce (s : Set V)).Connected →
      (L.induce (s : Set V)).edgeSet.ncard + 6 ≤
        3 * Fintype.card {v // v ∈ (s : Set V)}) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
