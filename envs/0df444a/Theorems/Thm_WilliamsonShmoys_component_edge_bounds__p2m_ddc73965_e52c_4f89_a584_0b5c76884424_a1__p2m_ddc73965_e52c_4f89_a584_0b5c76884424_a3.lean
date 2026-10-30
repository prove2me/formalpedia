-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_bounds__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3
-- name    : WilliamsonShmoys.component_edge_bounds__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:06.043006+00:00
-- url     : https://prove2.me/theorems/798c5648-bc79-4a8b-aaf2-40b61aa85372
-- title:
--   Component edge bounds
-- statement:
--   For each component support of size at most two, simplicity bounds the number of induced edges by one. For larger supports, the induced graph is connected, so the supplied local hypothesis gives the stated edge bound. The thresholds and additive constant are unchanged.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_edge_bounds__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLocal : ∀ (S : Finset V), 3 ≤ S.card → (L.induce (↑S : Set V)).Connected → (L.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card) : (∀ c : L.ConnectedComponent, (SimpleGraph.ConnectedComponent.supp c).ncard ≤ 2 → (L.induce (SimpleGraph.ConnectedComponent.supp c)).edgeSet.ncard ≤ 1) ∧ (∀ c : L.ConnectedComponent, 3 ≤ (SimpleGraph.ConnectedComponent.supp c).ncard → (L.induce (SimpleGraph.ConnectedComponent.supp c)).edgeSet.ncard + 6 ≤ 3 * (SimpleGraph.ConnectedComponent.supp c).ncard) := by sorry
