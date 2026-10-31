-- Prove2me | Theorems.Thm_TetrisHard_Rows_cleared_rows_inapproximability
-- name    : TetrisHard.Rows.cleared_rows_inapproximability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:56:40.319998+00:00
-- url     : https://prove2.me/theorems/17540620-b0b6-4a21-9bae-3139939df54d
-- title:
--   Theorem 6.5 — $p^{1−ε}$ inapproximability of cleared rows
-- statement:
--   For every fixed admissible reasonable rotation model R and every fixed real ε>0, the search problem of obtaining a feasible row count v with OPT(G)≤p^(1−ε)v is NP-hard. The domain consists of all legal finite initial boards and all ordered finite lists of the seven piece types; dimensions, occupancy and pieces are explicit input. Polynomial time is measured in the encoded input length, while the factor uses only the piece count p. NP-hardness requires polynomial-time instance and answer maps for every NP language, correct for every admissible approximation answer. Empty lists have answer zero. The statement assumes neither 3-Partition hardness nor a correct gadget reduction nor P≠NP.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - reading: maximum rows cleared and the Section 2 next-spawn loss rule → attainable prefix scores including the rows cleared immediately before a blocked next spawn; reason: row deletion precedes the loss check on page 6; a prefix can be extended without reducing its score
--   - encoding: NP-hard approximation for every fixed ε>0 → concrete binary query and feasible-count answer relations with Cook polynomial-time query and answer maps; reason: the real ε and rotation model are fixed before the reduction; no oracle for real arithmetic or assumed hardness premise is introduced
--   - encoding: p^(1−ε) and a finite piece sequence → the same real power for p>0, and the zero answer for p=0; reason: an empty sequence clears no rows; this avoids a totalized zero-to-negative-power convention without narrowing the domain
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Theorem 6.5, printed p. 21 = PDF p. 21, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem cleared_rows_inapproximability
    (R : Rotation) (hR : R.Admissible) (hReason : Reasonable R)
    (ε : ℝ) (hε : 0 < ε) :
    (rowSearch R ε).NPHard := by sorry

end TetrisHard.Rows
