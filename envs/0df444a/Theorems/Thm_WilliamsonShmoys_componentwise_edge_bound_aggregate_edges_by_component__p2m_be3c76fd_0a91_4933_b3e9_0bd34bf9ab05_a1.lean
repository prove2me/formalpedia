-- Prove2me | Theorems.Thm_WilliamsonShmoys_componentwise_edge_bound_aggregate_edges_by_component__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- name    : WilliamsonShmoys.componentwise_edge_bound_aggregate_edges_by_component__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:13:36.874143+00:00
-- url     : https://prove2.me/theorems/9dfa7b62-ba18-4e57-8b99-e2fc9224a608
-- title:
--   Bound total edges by component allowances
-- statement:
--   The graph’s edge count is at most the sum of component allowances. Large components use their local bound; a component of size one has no edges, and a component of size two has at most one.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
set_option autoImplicit false

theorem WilliamsonShmoys.componentwise_edge_bound_aggregate_edges_by_component__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hcomp : ∀ c : K.ConnectedComponent, 3 ≤ c.supp.ncard →
      (K.induce c.supp).edgeSet.ncard ≤ 3 * c.supp.ncard - 6) :
    K.edgeSet.ncard ≤
      ∑ c : K.ConnectedComponent,
        if 3 ≤ c.supp.ncard then 3 * c.supp.ncard - 6 else c.supp.ncard / 2 := by sorry
