-- Prove2me | Theorems.Thm_WilliamsonShmoys_directed_adj_card_eq_twice_edgeSet_ncard__p2m_badb0730_b4d5_45ef_abd7_880e94965ba4_a1
-- name    : WilliamsonShmoys.directed_adj_card_eq_twice_edgeSet_ncard__p2m_badb0730_b4d5_45ef_abd7_880e94965ba4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:22:21.516129+00:00
-- url     : https://prove2.me/theorems/9b1ef575-c3f2-44f4-890b-4dea59e241c0
-- title:
--   Directed edge count
-- statement:
--   For a finite simple graph, each undirected edge contributes exactly its two orientations to the subtype of ordered adjacent pairs. This supplies the target’s directed-edge cardinality equation independently of planarity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.directed_adj_card_eq_twice_edgeSet_ncard__p2m_badb0730_b4d5_45ef_abd7_880e94965ba4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    Fintype.card {e : V × V // H.Adj e.1 e.2} = 2 * H.edgeSet.ncard := by sorry
