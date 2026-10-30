-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_bounds__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1
-- name    : WilliamsonShmoys.component_edge_bounds__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:15:14.559119+00:00
-- url     : https://prove2.me/theorems/41e7cd07-6650-48eb-8449-d4a44468ed5e
-- title:
--   Component edge bounds
-- statement:
--   A component support of size at most two has at most one induced edge; for a support of size at least three, the local hypothesis gives the stated edge bound once its induced graph is shown connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.component_edge_bounds__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLocal : ∀ (S : Finset V), 3 ≤ S.card → (L.induce (↑S : Set V)).Connected → (L.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card) : (∀ c : L.ConnectedComponent, c.supp.ncard ≤ 2 → (L.induce c.supp).edgeSet.ncard ≤ 1) ∧ (∀ c : L.ConnectedComponent, 3 ≤ c.supp.ncard → (L.induce c.supp).edgeSet.ncard + 6 ≤ 3 * c.supp.ncard) := by sorry
