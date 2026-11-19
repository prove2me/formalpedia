-- Prove2me | Theorems.Thm_TetrisHard_Rows_reservoir_completeness
-- name    : TetrisHard.Rows.reservoir_completeness
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-18T20:08:20.138042+00:00
-- url     : https://prove2.me/theorems/48901ad6-0fd0-4813-8021-8465a97b6ab2
-- title:
--   Theorem 6.5, yes case — at least $r$ rows cleared in the reservoir game
-- statement:
--   Let $R$ be an admissible reasonable rotation model and let $\sigma=2\rho+8$ be the fixed staging allowance, where $\rho$ is the radius of $R$. Let $P$ be a valid normalized 3-Partition instance with $s\ge 1$ parts which is a yes-instance, and let $r$ be even.
--
--   Consider the game of Figure 9(b): the original gameboard $G(P)$ (with staging $\sigma$) widened by four completely filled columns, above a two-row second lock opened only by an RG, above an $r$-row reservoir empty except in the first column. The piece sequence is the original sequence, then one RG, then $r(6s+6)/4$ squares. Then
--   $$\exists\, v\ge r:\quad v \text{ is an attainable cleared-row count of this game.}$$
--
--   Indeed, the original board can be cleared completely, the RG opens the second lock, and the squares tile and clear all reservoir rows. This is the yes case in the proofs of Theorems 6.3–6.5.
--
--   **Formalization Note** The hypothesis $s\ge1$ excludes the degenerate empty instance, for which the base board has width $3$ and the I pieces cannot spawn (see the mission discussion on Theorem 4.1). Attainable scores count rows cleared by finite legal prefixes of play.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 6.2 (p. 21, yes case of Theorem 6.3) and proof of Theorem 6.5 (p. 21: 'in the yes case of 3-Partition, we can completely fill and clear the gameboard'), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_GapReduction

namespace TetrisHard.Rows

theorem reservoir_completeness (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (hs : 0 < P.s)
    (hyes : P.HasSolution) (r : ℕ) (hr : Even r) :
    ∃ v, r ≤ v ∧ Attainable R (reservoirGame P (stagingAllowance R) r) v := by sorry

end TetrisHard.Rows
