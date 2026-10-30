-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edge_bounds_small__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1
-- name    : WilliamsonShmoys.component_edge_bounds_small__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:06.405431+00:00
-- url     : https://prove2.me/theorems/403b5955-1e8d-43b4-a8d2-12f858c32c9f
-- title:
--   Edge bound for small component supports
-- statement:
--   A simple graph induced on a connected-component support with at most two vertices has at most one edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.component_edge_bounds_small__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (c : L.ConnectedComponent) (hsmall : (SimpleGraph.ConnectedComponent.supp c).ncard ≤ 2) : (L.induce (SimpleGraph.ConnectedComponent.supp c)).edgeSet.ncard ≤ 1 := by sorry
