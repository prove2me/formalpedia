-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_eq_of_graph_eq__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a3
-- name    : WilliamsonShmoys.edgeFinset_card_eq_of_graph_eq__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:27:11.162188+00:00
-- url     : https://prove2.me/theorems/07491726-d28c-4827-badb-02b90443303d
-- title:
--   Edge count is invariant under graph equality
-- statement:
--   For finite linearly ordered vertex types, equal simple graphs have equal edge counts even when those counts are formed using separately supplied decidability instances.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeFinset_card_eq_of_graph_eq__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (dG : DecidableRel G.Adj) (dH : DecidableRel H.Adj)
    (h : G = H) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) =
      (letI : DecidableRel H.Adj := dH; H.edgeFinset.card) := by sorry
