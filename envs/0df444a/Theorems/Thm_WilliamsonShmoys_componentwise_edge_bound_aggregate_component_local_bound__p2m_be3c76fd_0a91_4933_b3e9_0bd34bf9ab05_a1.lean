-- Prove2me | Theorems.Thm_WilliamsonShmoys_componentwise_edge_bound_aggregate_component_local_bound__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- name    : WilliamsonShmoys.componentwise_edge_bound_aggregate_component_local_bound__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:13:37.434126+00:00
-- url     : https://prove2.me/theorems/4dbc53a5-11e8-4c0d-89ea-b7279c265ca6
-- title:
--   Apply the local bound to a connected component
-- statement:
--   Each connected component with at least three vertices satisfies the assumed induced-subgraph edge bound. Its support is connected in the induced graph, so the hypothesis applies to the support finset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
set_option autoImplicit false

theorem WilliamsonShmoys.componentwise_edge_bound_aggregate_component_local_bound__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hlocal : ∀ S : Finset V, 3 ≤ S.card →
      (K.induce (↑S : Set V)).Connected →
      (K.induce (↑S : Set V)).edgeSet.ncard ≤ 3 * S.card - 6)
    (c : K.ConnectedComponent) (hc : 3 ≤ c.supp.ncard) :
    (K.induce c.supp).edgeSet.ncard ≤ 3 * c.supp.ncard - 6 := by sorry
