-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_reachable_classes_partition__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- name    : WilliamsonShmoys.connected_component_partition_reachable_classes_partition__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:26:36.84821+00:00
-- url     : https://prove2.me/theorems/19bbae96-a260-4c1e-a916-592b144a4edc
-- title:
--   Reachability classes coincide or are disjoint
-- statement:
--   Any two reachability classes are equal or disjoint. This supplies pairwise disjointness of distinct parts in the parent. For the equal case, split on whether the classes intersect: a common reachable vertex and symmetry and transitivity of reachability show the representatives are mutually reachable, which makes the classes equal. If there is no common member, the finsets are disjoint by definition. The statement has no restrictions beyond the given vertices, so it also covers isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
open Classical
open SimpleGraph

theorem WilliamsonShmoys.connected_component_partition_reachable_classes_partition__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (u v : V) : Finset.univ.filter (fun w => M.Reachable u w) = Finset.univ.filter (fun w => M.Reachable v w) ∨ Disjoint (Finset.univ.filter (fun w => M.Reachable u w)) (Finset.univ.filter (fun w => M.Reachable v w)) := by sorry
