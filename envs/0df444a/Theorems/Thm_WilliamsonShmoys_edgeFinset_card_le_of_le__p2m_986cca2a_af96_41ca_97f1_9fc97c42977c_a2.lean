-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_of_le__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
-- name    : WilliamsonShmoys.edgeFinset_card_le_of_le__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:12:00.34743+00:00
-- url     : https://prove2.me/theorems/42fbe241-3860-4a9f-b21c-25c4bb4f5ec5
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, inclusion of adjacency relations implies that the finite edge count cannot decrease.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.edgeFinset_card_le_of_le__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
    {V : Type} [Fintype V]
    (K H : SimpleGraph V)
    [DecidableRel K.Adj] [DecidableRel H.Adj]
    (hKH : K ≤ H) :
    Nat.le K.edgeFinset.card H.edgeFinset.card := by
  sorry
