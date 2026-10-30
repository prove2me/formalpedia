-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_bounds_large__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1
-- name    : WilliamsonShmoys.component_edge_bounds_large__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:06.860333+00:00
-- url     : https://prove2.me/theorems/6a70bc9e-bafc-44c9-9e52-5ddfb96b8782
-- title:
--   Local edge bound for large component supports
-- statement:
--   For a component support of size at least three, the local edge bound applies to the induced graph on that support.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.component_edge_bounds_large__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLocal : ∀ (S : Finset V), 3 ≤ S.card → (L.induce (↑S : Set V)).Connected → (L.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card) (c : L.ConnectedComponent) (hlarge : 3 ≤ (SimpleGraph.ConnectedComponent.supp c).ncard) : (L.induce (SimpleGraph.ConnectedComponent.supp c)).edgeSet.ncard + 6 ≤ 3 * (SimpleGraph.ConnectedComponent.supp c).ncard := by sorry
