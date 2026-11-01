-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_adj_in_reachable_class__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- name    : WilliamsonShmoys.connected_component_partition_adj_in_reachable_class__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:26:38.85553+00:00
-- url     : https://prove2.me/theorems/ead83be0-46ab-4996-be68-ab70996fd7a5
-- title:
--   Adjacent vertices share a reachability class
-- statement:
--   If u and v are adjacent, then v belongs to u’s reachability class. This supplies edge containment in the parent; u belongs to that same class by the self-membership child. Unfold filter membership, use membership in `Finset.univ`, and obtain reachability from the single-edge path given by h. The statement retains exactly the required adjacency hypothesis and applies to every graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
open Classical
open SimpleGraph

theorem WilliamsonShmoys.connected_component_partition_adj_in_reachable_class__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) {u v : V} (h : M.Adj u v) : v ∈ Finset.univ.filter (fun w => M.Reachable u w) := by sorry
