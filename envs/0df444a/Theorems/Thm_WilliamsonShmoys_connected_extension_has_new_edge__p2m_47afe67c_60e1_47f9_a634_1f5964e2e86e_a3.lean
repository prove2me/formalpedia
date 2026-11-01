-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_extension_has_new_edge__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
-- name    : WilliamsonShmoys.connected_extension_has_new_edge__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:57:52.642289+00:00
-- url     : https://prove2.me/theorems/e01e14b2-e548-4ab2-80ee-ce2afb5aef97
-- title:
--   A connected graph extension adds an edge to a disconnected graph
-- statement:
--   If a graph is a subgraph of a connected graph but is disconnected, the larger graph has an edge whose endpoints are distinct and which was not an edge of the smaller graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.connected_extension_has_new_edge__p2m_47afe67c_60e1_47f9_a634_1f5964e2e86e_a3
    {V : Type} [Fintype V]
    (K M : SimpleGraph V)
    (hKM : K ≤ M)
    (hK : ¬ K.Connected)
    (hM : M.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Adj u v ∧ M.Adj u v := by sorry
