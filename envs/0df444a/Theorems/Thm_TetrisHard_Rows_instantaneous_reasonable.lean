-- Prove2me | Theorems.Thm_TetrisHard_Rows_instantaneous_reasonable
-- name    : TetrisHard.Rows.instantaneous_reasonable
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:56:49.476923+00:00
-- url     : https://prove2.me/theorems/6a8bf228-c0e4-4a9a-860b-18d6d8e77e58
-- title:
--   Lemma 5.10 — The concrete instantaneous model is reasonable
-- statement:
--   Lemma 5.10 The instantaneous rotation model of Section 2 is reasonable.
--
--   The instantaneous rotation rule with the exact centers of Figure 2 satisfies the Section 2 rotation-model requirements and all four geometric conditions of reasonability. The square footprint remains fixed under rotation.
--
--   Differences from the source:
--   - encoding: one-based rows and columns → zero-based stored cells and signed integer positions; reason: subtracting one preserves every board cell; sentinels prevent subtraction from creating legal cells below the floor
--   - encoding: instantaneous rotation is a reasonable rotation model → admissibility and reasonability are asserted together; reason: the raw rotation-table type separates Section 2 model requirements from the four Section 5.3 conditions
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Lemma 5.10, printed p. 16 = PDF p. 16, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir

namespace TetrisHard.Rows

theorem instantaneous_reasonable :
    instantaneous.Admissible ∧ Reasonable instantaneous := by sorry

end TetrisHard.Rows
