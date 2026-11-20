-- Prove2me | Theorems.Thm_TetrisHard_Rows_Padded_paddedNoBound_code_polytime
-- name    : TetrisHard.Rows.Padded.paddedNoBound_code_polytime
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T06:50:03.837945+00:00
-- url     : https://prove2.me/theorems/e1f33a0b-ca59-46a3-95ed-4630d3b9f5c8
-- title:
--   Theorem 6.5 — the padded no-case threshold is polynomial-time computable
-- statement:
--   For every fixed padding parameter $\mathrm{pad}$, chimney parameter $K$, and staging allowance $\sigma$, the map sending a binary word $w \in \{0,1\}^*$ to the unary encoding $\langle \mathrm{paddedNoBound}(\mathrm{norm}(w), \mathrm{pad}, K, \sigma)\rangle$ of the no-case cleared-row bound is computable in polynomial time:
--   $$w \mapsto \langle \mathrm{paddedNoBound}(\mathrm{norm}(w), \mathrm{pad}, K, \sigma)\rangle \in \mathrm{FP}.$$
--
--   This supplies the polynomial-time threshold used by the gap decision procedure in Theorem 6.5.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 3 (p. 7), Section 5.3 (pp. 12-14), Section 6.2 and Figure 9(b) (pp. 19-21), Theorem 6.5 (p. 21), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_PaddedGapReduction

namespace TetrisHard.Rows.Padded

theorem paddedNoBound_code_polytime (pad K st : ℕ) :
    CookPvsNP.PolyTimeComputable
      (fun w : List Bool => unaryCode [paddedNoBound (normInstance w) pad K st]) := by sorry

end TetrisHard.Rows.Padded
