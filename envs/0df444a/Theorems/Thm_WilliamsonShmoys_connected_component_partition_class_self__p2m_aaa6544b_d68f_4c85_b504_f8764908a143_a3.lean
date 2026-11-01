-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_class_self__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- name    : WilliamsonShmoys.connected_component_partition_class_self__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:26:30.333347+00:00
-- url     : https://prove2.me/theorems/c8a48e3e-6813-425e-a0be-2528def4202a
-- title:
--   A vertex belongs to its reachability class
-- statement:
--   Every vertex belongs to its own finite reachability class. This supplies the parent’s coverage witness and proves every image class is nonempty. The independent proof route is to unfold `Finset.mem_filter`, use membership in `Finset.univ`, and apply reachability reflexivity. There is no nonempty-vertex-type hypothesis: if V is empty, there is no v to consider.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
open Classical
open SimpleGraph

theorem WilliamsonShmoys.connected_component_partition_class_self__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (v : V) : v ∈ Finset.univ.filter (fun w => M.Reachable v w) := by sorry
