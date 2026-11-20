-- Prove2me | Theorems.Thm_TetrisHard_Rows_Padded_paddedReservoir_soundness
-- name    : TetrisHard.Rows.Padded.paddedReservoir_soundness
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:50:16.437144+00:00
-- url     : https://prove2.me/theorems/862f5dbd-8e35-4e57-9f0c-747983905614
-- title:
--   Theorem 6.5, no case — cumulative cleared rows bounded independently of r in the padded reservoir game
-- statement:
--   Let $R$ be an admissible reasonable rotation model, let $P$ be a valid normalized no-instance of 3-Partition with $s \ge 1$, and let $\mathrm{pad} \ge \max(\rho,2)+2$, $K \ge \mathrm{maxJump}(R)+2$, $\sigma \ge 5\max(\rho,2)+12$, and $r \ge 0$. Every attainable cleared-row count $v$ of $\mathrm{paddedReservoirGame}(P,\mathrm{pad},K,\sigma,r)$ satisfies
--   $$v \le \mathrm{paddedNoBound}(P, \mathrm{pad}, K, \sigma),$$
--   a polynomial bound independent of $r$.
--
--   Because the $12\cdot\mathrm{pad}$ buffer shaft and $6\cdot\mathrm{pad}$ filled columns preserve the `BucketFrame` local neighborhood invariant for $s+\mathrm{pad}$ buckets and leave at most one piece of area slack above the second lock, no-instances cannot clear all chimney rows before the square sequence begins; the surviving one-wide chimney blocks squares from entering the reservoir, and odd board width bounds square row clears above the second lock via row-occupancy parity.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 3 (p. 7), Section 5.3 (pp. 12-14), Section 6.2 and Figure 9(b) (pp. 19-21), Theorem 6.5 (p. 21), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_PaddedGapReduction

namespace TetrisHard.Rows.Padded

theorem paddedReservoir_soundness
    (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (hs : 0 < P.s)
    (hno : ¬ P.HasSolution)
    (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad)
    (hK : maxJump R + 2 ≤ K)
    (hst : 5 * max R.radius 2 + 12 ≤ st) :
    ∀ v, Attainable R (paddedReservoirGame P pad K st r) v →
      v ≤ paddedNoBound P pad K st := by sorry

end TetrisHard.Rows.Padded
