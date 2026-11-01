-- Prove2me | Theorems.Thm_WilliamsonShmoys_card_le_edgeFinset_add_one_of_connected__p2m_de496d36_7d00_43e9_8f8b_fa9ee9576ec1_a3
-- name    : WilliamsonShmoys.card_le_edgeFinset_add_one_of_connected__p2m_de496d36_7d00_43e9_8f8b_fa9ee9576ec1_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:49:29.94321+00:00
-- url     : https://prove2.me/theorems/d237c4ad-db2e-4dfd-980e-16432a7cccf2
-- title:
--   Connected finite graphs have at least one fewer edge than vertices
-- statement:
--   Every finite connected simple graph has at least |V| − 1 edges. This removes the combinatorial part of the parent proof; a spanning tree provides an independent proof route by counting its |V| − 1 edges and using that all its edges belong to K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.card_le_edgeFinset_add_one_of_connected__p2m_de496d36_7d00_43e9_8f8b_fa9ee9576ec1_a3
    {V : Type} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hconn : K.Connected) :
    Fintype.card V ≤ K.edgeFinset.card + 1 := by
  sorry
