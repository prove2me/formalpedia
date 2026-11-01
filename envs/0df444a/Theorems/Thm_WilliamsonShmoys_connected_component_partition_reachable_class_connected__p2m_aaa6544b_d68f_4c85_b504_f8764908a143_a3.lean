-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_reachable_class_connected__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- name    : WilliamsonShmoys.connected_component_partition_reachable_class_connected__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:26:34.247368+00:00
-- url     : https://prove2.me/theorems/0de68233-b846-4adf-ae00-e1d64ee2fed7
-- title:
--   The induced reachability class is connected
-- statement:
--   The graph induced by the vertices reachable from v is connected. This removes the induced-connectedness obligation from the parent. A proof route takes any vertex of the class, chooses a reachability path from v to it, and shows every vertex along the path remains reachable from v; the path then lies in the induced graph. Reflexivity ensures v itself belongs to the class. The remaining work is translating reachability and paths into the induced graph’s connectivity API. The statement applies to every vertex and graph, including isolated vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
open Classical
open SimpleGraph

theorem WilliamsonShmoys.connected_component_partition_reachable_class_connected__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (v : V) : (M.induce ((Finset.univ.filter (fun w => M.Reachable v w) : Finset V) : Set V)).Connected := by sorry
