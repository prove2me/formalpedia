-- Prove2me | Theorems.Thm_TetrisHard_Rows_Padded_paddedReservoir_chimney_reduction
-- name    : TetrisHard.Rows.Padded.paddedReservoir_chimney_reduction
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:28:52.304346+00:00
-- url     : https://prove2.me/theorems/97918bdc-49ce-40a4-a61b-b3e69f57b723
-- title:
--   Section 6.2 — chimney barrier dichotomy and zero-waste Phase-1 bucket lifting
-- statement:
--   Let $R$ be an admissible reasonable rotation model of radius $\rho$, let $P$ be a valid normalized 3-Partition instance with $s \ge 1$, and let $\mathrm{pad} \ge \max(\rho,2)+2$, $K \ge \mathrm{maxJump}(R)+2$, $\sigma \ge 5\max(\rho,2)+12$, and $r \ge 0$. For every cleared-row count $v$ attainable in $\mathrm{paddedReservoirGame}(P,\mathrm{pad},K,\sigma,r)$, let $U_0 = \mathrm{dropRows}(\mathrm{paddedReservoirBoard}(P,\mathrm{pad},K,\sigma,r),\, r+2+4K)$ and $H' = 12\cdot\mathrm{pad} + \mathrm{baseHeight}(P)$. Then either
--   $$v \le \mathrm{paddedNoBound}(P, \mathrm{pad}, K, \sigma),$$
--   or $U_0$ has every bucket $j < s$ unprepped at initial height $12\cdot\mathrm{pad}+4$ and the Phase-1 piece sequence $\mathrm{numberPieces}(P) \mathbin{+\!\!+} \mathrm{I}^s$ lifts to a zero-waste bucket play on $U_0$ that fills all $s$ buckets up to height $H'$:
--   $$\exists\, \mathbf{u},\mathbf{u}_{\mathrm{I}},U_{\mathrm{num}},U_{\mathrm{end}},\quad \mathrm{NoRGSeqPlay}_R(s,s+\mathrm{pad},H',U_0,\mathrm{numberPieces}(P),\mathbf{u},U_{\mathrm{num}}) \;\wedge\; \mathrm{NoRGSeqPlay}_R(s,s+\mathrm{pad},H',U_{\mathrm{num}},\mathrm{I}^s,\mathbf{u}_{\mathrm{I}},U_{\mathrm{end}}) \;\wedge\; \forall j < s,\ \mathrm{BucketFull}(U_{\mathrm{end}},j,H').$$
--
--   If no prefix of the pre-square pieces clears all $4K$ chimney rows and $H'$ upper rows, the surviving one-wide chimney blocks squares from entering the reservoir and row-occupancy parity bounds square row clears above row $r+2$. Otherwise, modulo-4 empty-cell invariance eliminates the 4 slack cells of the final $\mathrm{RG}$ key, forcing zero waste across all Phase-1 pieces.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 5.3-5.4 (pp. 12-18), Section 6.2 (pp. 19-21), and Appendix C.1-C.2 (pp. 25-33), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_PaddedSoundness

namespace TetrisHard.Rows.Padded

theorem paddedReservoir_chimney_reduction
    (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (P : ThreePartition) (hP : P.Valid) (hN : P.Normalized) (hs : 0 < P.s)
    (pad K st r : ℕ)
    (hpad : max R.radius 2 + 2 ≤ pad)
    (hK : maxJump R + 2 ≤ K)
    (hst : 5 * max R.radius 2 + 12 ≤ st)
    (v : ℕ) (hatt : Attainable R (paddedReservoirGame P pad K st r) v) :
    v ≤ paddedNoBound P pad K st ∨
    (AllUnpreppedHeights (dropRows (paddedReservoirBoard P pad K st r) (r + 2 + 4 * K))
        P.s (12 * pad + baseHeight P) (fun _ => 12 * pad + 4) ∧
     ∃ us us_I U_num U_end,
       NoRGSeqPlay R P.s (P.s + pad) (12 * pad + baseHeight P)
         (dropRows (paddedReservoirBoard P pad K st r) (r + 2 + 4 * K))
         (numberPieces P) us U_num ∧
       NoRGSeqPlay R P.s (P.s + pad) (12 * pad + baseHeight P)
         U_num (List.replicate P.s .I) us_I U_end ∧
       ∀ j : Fin P.s, BucketFull U_end j.val (12 * pad + baseHeight P)) := by sorry

end TetrisHard.Rows.Padded
