-- Prove2me | Theorems.Thm_TetrisHard_Rows_Padded_paddedGapGame_code_polytime
-- name    : TetrisHard.Rows.Padded.paddedGapGame_code_polytime
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:50:20.02986+00:00
-- url     : https://prove2.me/theorems/59fba16a-862b-46e2-9551-80cfac767dfc
-- title:
--   Theorem 6.5 — the amplified padded reservoir game is polynomial-time constructible
-- statement:
--   For every fixed tuple of parameters $(\mathrm{pad}, K, \sigma, k)$, the map sending a binary word $w \in \{0,1\}^*$ to the binary game encoding of the amplified padded reservoir game $\mathrm{paddedGapGame}_{\mathrm{pad},K,\sigma,k}(w)$ is polynomial-time computable:
--   $$w \mapsto \mathrm{code}\bigl(\mathrm{paddedGapGame}_{\mathrm{pad},K,\sigma,k}(w)\bigr) \in \mathrm{FP}.$$
--
--   Because $r_k(\mathrm{norm}(w)) = 2(a(P)M(P)+1)^k$ is polynomial in the unary size of $\mathrm{norm}(w)$ for fixed $(\mathrm{pad},K,\sigma,k)$, both the board occupancy matrix and the piece sequence have polynomial length and are emitted in polynomial time.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 3 (p. 7), Section 5.3 (pp. 12-14), Section 6.2 and Figure 9(b) (pp. 19-21), Theorem 6.5 (p. 21), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_PaddedGapReduction

namespace TetrisHard.Rows.Padded

theorem paddedGapGame_code_polytime (pad K st k : ℕ) :
    CookPvsNP.PolyTimeComputable
      (fun w : List Bool => (paddedGapGame pad K st k w).code) := by sorry

end TetrisHard.Rows.Padded
