-- Prove2me | Theorems.Thm_WilliamsonShmoys_bridge_add_graph__p2m_02853d91_2027_4c7f_9261_be16db6326ab_a3
-- name    : WilliamsonShmoys.bridge_add_graph__p2m_02853d91_2027_4c7f_9261_be16db6326ab_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:31:02.127707+00:00
-- url     : https://prove2.me/theorems/85ae4dd4-8ffb-4642-8267-b17c048c599c
-- title:
--   Construct the graph with the selected added pair
-- statement:
--   Construct a simple graph containing G whose edges are exactly the old edges together with the selected pair.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.bridge_add_graph__p2m_02853d91_2027_4c7f_9261_be16db6326ab_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (x y : V)
    (hxy : ¬ G.Reachable x y) :
    ∃ N : SimpleGraph V,
      G ≤ N ∧
      (∀ u v, N.Adj u v ↔
        G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) := by
  sorry
