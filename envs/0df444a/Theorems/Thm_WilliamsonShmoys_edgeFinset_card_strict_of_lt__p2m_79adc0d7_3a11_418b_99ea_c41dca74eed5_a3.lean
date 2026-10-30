-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_strict_of_lt__p2m_79adc0d7_3a11_418b_99ea_c41dca74eed5_a3
-- name    : WilliamsonShmoys.edgeFinset_card_strict_of_lt__p2m_79adc0d7_3a11_418b_99ea_c41dca74eed5_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:13:58.120923+00:00
-- url     : https://prove2.me/theorems/4652e9dd-b4ff-4ab4-8c66-c5b0e3748747
-- title:
--   Strict graph inclusion increases edge count
-- statement:
--   For finite simple graphs with edge-set `Fintype` instances, proper graph inclusion strictly increases the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edgeFinset_card_strict_of_lt__p2m_79adc0d7_3a11_418b_99ea_c41dca74eed5_a3 {V : Type} [Fintype V] [DecidableEq V] (G H : SimpleGraph V) [Fintype G.edgeSet] [Fintype H.edgeSet] (hGH : LE.le G H) (hne : G ≠ H) : G.edgeFinset.card < H.edgeFinset.card := by sorry
