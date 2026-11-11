-- Prove2me | Theorems.Thm_WilliamsonShmoys_componentwise_edge_bound_aggregate_component_card_sum__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- name    : WilliamsonShmoys.componentwise_edge_bound_aggregate_component_card_sum__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:13:37.809849+00:00
-- url     : https://prove2.me/theorems/2972acd7-b6b8-432c-8fb5-e8fb44989789
-- title:
--   Component supports partition the vertices
-- statement:
--   The cardinalities of all connected-component supports sum to the number of vertices, because those supports partition the vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
set_option autoImplicit false

theorem WilliamsonShmoys.componentwise_edge_bound_aggregate_component_card_sum__p2m_be3c76fd_0a91_4933_b3e9_0bd34bf9ab05_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj] :
    (∑ c : K.ConnectedComponent, c.supp.ncard) = Fintype.card V := by sorry
