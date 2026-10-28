-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_retry2_edge_monotone
-- name    : WilliamsonShmoys.connected_planar_edge_bound_retry2_edge_monotone
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:49:10.760159+00:00
-- url     : https://prove2.me/theorems/0f5d904d-88eb-4e47-9175-9f45a62ca03e
-- title:
--   Edge count is monotone under subgraphs
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertex type, its edge-set cardinality is no larger. Prove this by turning the subgraph relation into edge-set inclusion and applying finite-cardinality monotonicity; this discharges the parent’s counting step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_retry2_edge_monotone
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hSub : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
