-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_lt_of_le_of_ne__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1
-- name    : WilliamsonShmoys.edgeFinset_card_lt_of_le_of_ne__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:08.677737+00:00
-- url     : https://prove2.me/theorems/35af1a8d-885a-4459-93dd-bf2ec2b961d2
-- title:
--   Strict graph inclusion increases edge count
-- statement:
--   If one graph is a proper subgraph of another and both edge sets are finite, the larger graph has strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
open SimpleGraph

theorem WilliamsonShmoys.edgeFinset_card_lt_of_le_of_ne__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1 {V : Type} (A B : SimpleGraph V) (hAfin : Fintype A.edgeSet) (hBfin : Fintype B.edgeSet) (hAB : A ≤ B) (hne : A ≠ B) : @Fintype.card A.edgeSet hAfin < @Fintype.card B.edgeSet hBfin := by sorry
