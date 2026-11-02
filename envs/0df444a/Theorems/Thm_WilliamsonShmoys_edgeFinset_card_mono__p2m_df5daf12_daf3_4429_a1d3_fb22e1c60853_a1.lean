-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_mono__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1
-- name    : WilliamsonShmoys.edgeFinset_card_mono__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:41:25.077178+00:00
-- url     : https://prove2.me/theorems/1a16aafc-6a73-4502-855c-f93fc65ac096
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite graphs on the same vertex type, inclusion of adjacency relations implies inclusion of their edge finsets and hence monotonicity of edge count. This isolates the finite-set step used after maximality gives K ≤ H. It can be proved from Mathlib’s edge-finset inclusion theorem and Finset.card_le_card.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edgeFinset_card_mono__p2m_df5daf12_daf3_4429_a1d3_fb22e1c60853_a1
    {V : Type} [Fintype V]
    (G F : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F.Adj]
    (hGF : G ≤ F) :
    G.edgeFinset.card ≤ F.edgeFinset.card := by sorry
