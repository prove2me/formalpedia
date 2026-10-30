-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_component_partition_local_bound__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1
-- name    : WilliamsonShmoys.connected_component_partition_local_bound__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:55:41.162275+00:00
-- url     : https://prove2.me/theorems/0df0647f-1812-42b2-814f-8778fabaf306
-- title:
--   Local bound for a nonempty connected induced subgraph
-- statement:
--   For a nonempty connected induced subgraph, the assumed deficit-6 bound handles sizes at least 3. At sizes 1 and 2, simplicity bounds the edge count by 0 and 1, respectively, which gives the deficit-3 bound. A proof splits on the stated size cutoff and uses the simple-graph edge bound by the number of unordered vertex pairs in the small cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.connected_component_partition_local_bound__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1 {V : Type} [Fintype V] (H : SimpleGraph V) (hBound : ∀ (s : Finset V), (H.induce (↑s : Set V)).Connected → 3 ≤ Fintype.card {v // v ∈ s} → (H.induce (↑s : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card {v // v ∈ s}) (s : Finset V) (hNonempty : 1 ≤ Fintype.card {v // v ∈ s}) (hConnected : (H.induce (↑s : Set V)).Connected) : (H.induce (↑s : Set V)).edgeSet.ncard + (if 3 ≤ Fintype.card {v // v ∈ s} then 6 else 3) ≤ 3 * Fintype.card {v // v ∈ s} := by sorry
