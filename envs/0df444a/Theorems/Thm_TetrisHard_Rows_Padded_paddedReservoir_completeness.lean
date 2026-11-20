-- Prove2me | Theorems.Thm_TetrisHard_Rows_Padded_paddedReservoir_completeness
-- name    : TetrisHard.Rows.Padded.paddedReservoir_completeness
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:51:15.889822+00:00
-- url     : https://prove2.me/theorems/18e41eed-32fa-4b6e-a43d-b97ff2ea0e42
-- title:
--   Theorem 6.5, yes case — at least r rows cleared in the padded reservoir game
-- statement:
--   Let $R$ be an admissible rotation model of radius $\rho$, let $P$ be a valid normalized yes-instance of 3-Partition with $s \ge 1$, and let $\mathrm{pad} \ge \max(\rho,2)+2$, $K \ge 1$, $\sigma \ge 5\max(\rho,2)+12$, and even $r \ge 0$. Then in $\mathrm{paddedReservoirGame}(P,\mathrm{pad},K,\sigma,r)$, at least $r$ rows can be cleared:
--   $$\exists\, w \ge r,\qquad \mathrm{Attainable}_R\bigl(\mathrm{paddedReservoirGame}(P,\mathrm{pad},K,\sigma,r),\, w\bigr).$$
--
--   The enlarged width and staging height provide an all-empty $(2\rho+1)\times(2\rho+1)$ neighborhood for up to three clockwise rotations of every piece; a valid 3-partition fills and clears the upper board, the extra $\mathrm{I}$ pieces and $\mathrm{RG}$ key clear the buffer shaft, chimney, and second lock, and the squares tile and clear all $r$ reservoir rows.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 3 (p. 7), Section 5.3 (pp. 12-14), Section 6.2 and Figure 9(b) (pp. 19-21), Theorem 6.5 (p. 21), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_PaddedGapReduction

namespace TetrisHard.Rows.Padded

theorem paddedReservoir_completeness
    (R : Rotation) (hR : R.Admissible)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (hs : 0 < P.s)
    (hyes : P.HasSolution)
    (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad)
    (hK : 1 ≤ K)
    (hst : 5 * max R.radius 2 + 12 ≤ st)
    (hr : Even r) :
    ∃ w, r ≤ w ∧ Attainable R (paddedReservoirGame P pad K st r) w := by sorry

end TetrisHard.Rows.Padded
