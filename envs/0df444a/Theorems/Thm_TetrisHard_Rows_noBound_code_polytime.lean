-- Prove2me | Theorems.Thm_TetrisHard_Rows_noBound_code_polytime
-- name    : TetrisHard.Rows.noBound_code_polytime
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-18T20:08:23.120199+00:00
-- url     : https://prove2.me/theorems/984e3d35-47a7-4678-80c4-bb5eb448d644
-- title:
--   Theorem 6.5 — the no-case threshold is polynomial-time computable
-- statement:
--   For every fixed staging allowance $\sigma$, the map sending a binary word $w$ to the unary code of the no-case bound $a(\mathrm{norm}(w))=2(h_0+2)+4(n_0+1)$ is polynomial-time computable, where $\mathrm{norm}(w)$ is the normalized 3-Partition instance decoded from $w$, $h_0$ the height of its base board and $n_0$ the length of its base piece sequence.
--
--   This threshold is the integer used by the decision procedure in the gap argument of Theorem 6.5: a feasible approximate row count is compared with it.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, proof of Theorem 6.5 (p. 21), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_GapReduction

namespace TetrisHard.Rows

theorem noBound_code_polytime (staging : ℕ) :
    CookPvsNP.PolyTimeComputable
      (fun w : List Bool => unaryCode [noBound (normInstance w) staging]) := by sorry

end TetrisHard.Rows
