-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_data__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1
-- name    : WilliamsonShmoys.component_edge_data__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:56:32.938572+00:00
-- url     : https://prove2.me/theorems/ddc73965-e52c-4f89-a584-0b5c76884424
-- title:
--   Account for vertex and edge counts across connected components
-- statement:
--   For a finite graph whose induced connected subgraphs of size at least three satisfy the local edge bound, assign each connected component its vertex count and induced edge count. These counts sum to the graph’s counts, every component is nonempty, small components have at most one edge, and large components satisfy the local bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_edge_data__p2m_66ed8684_7720_4905_99a4_14d61ffeb91a_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) [Fintype L.ConnectedComponent] (hLocal : ∀ (S : Finset V), 3 ≤ S.card → (L.induce (↑S : Set V)).Connected → (L.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card) : ∃ n e : L.ConnectedComponent → Nat, (∑ c : L.ConnectedComponent, n c) = Fintype.card V ∧ (∑ c : L.ConnectedComponent, e c) = L.edgeSet.ncard ∧ (∀ c, 1 ≤ n c) ∧ (∀ c, n c ≤ 2 → e c ≤ 1) ∧ (∀ c, 3 ≤ n c → e c + 6 ≤ 3 * n c) := by sorry
