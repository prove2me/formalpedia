-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_mono__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a2
-- name    : WilliamsonShmoys.edgeFinset_card_mono__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:58:49.543167+00:00
-- url     : https://prove2.me/theorems/eef8b32c-cd59-40a7-9329-fb6607c3a247
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, inclusion of adjacency relations implies that the subgraph's edge count is at most the supergraph's edge count. There is no vertex-count or planarity condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.edgeFinset_card_mono__p2m_d82f089b_ad0e_432a_8486_b2fabea854db_a2
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card) ≤
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card) := by sorry
