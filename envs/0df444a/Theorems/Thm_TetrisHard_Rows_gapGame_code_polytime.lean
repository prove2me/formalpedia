-- Prove2me | Theorems.Thm_TetrisHard_Rows_gapGame_code_polytime
-- name    : TetrisHard.Rows.gapGame_code_polytime
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-18T20:08:19.408194+00:00
-- url     : https://prove2.me/theorems/1e107d18-fadf-4491-bbdd-a0654535aaea
-- title:
--   Theorem 6.5 — the amplified reservoir game is polynomial-time constructible
-- statement:
--   For every fixed staging allowance $\sigma$ and exponent parameter $k$, the map sending a binary word $w$ to the code of the amplified reservoir game $\mathrm{gapGame}_{\sigma,k}(w)$ is polynomial-time computable (Cook's one-tape Turing machines).
--
--   Here the word is decoded as a unary 3-Partition instance, normalized by scaling with $6s$ (degenerate or invalid words are sent to fixed yes/no instances), and the game of Figure 9(b) is built with reservoir height $2(a(P)M(P)+1)^k$. The game code lists the dimensions in unary, the full occupancy matrix, and the piece sequence.
--
--   This is the polynomiality remark in the proof of Theorem 6.5 ('r, and thus our game, is still polynomial in the size of the 3-Partition instance'), resting on Theorem 3.2 and the strong NP-hardness of 3-Partition (unary entries).
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Theorem 3.2 (p. 8) and proof of Theorem 6.5 (p. 21), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_GapReduction

namespace TetrisHard.Rows

theorem gapGame_code_polytime (staging k : ℕ) :
    CookPvsNP.PolyTimeComputable (fun w : List Bool => (gapGame staging k w).code) := by sorry

end TetrisHard.Rows
