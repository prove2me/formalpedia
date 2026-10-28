-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_graph_spanning_subgraph
-- name    : WilliamsonShmoys.connected_graph_spanning_subgraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:19:50.567164+00:00
-- url     : https://prove2.me/theorems/a2502d49-7ec7-4794-94e9-4c5a6c009e1e
-- title:
--   Connected spanning subgraph of a finite connected graph
-- statement:
--   Every finite connected graph has a connected spanning subgraph; the subgraph uses the same vertex type and only edges of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.connected_graph_spanning_subgraph
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (hH : H.Connected) :
    ∃ T : SimpleGraph V,
      T.Connected ∧
      (∀ u v, T.Adj u v → H.Adj u v) := by sorry
