-- Prove2me | Theorems.Thm_TetrisHard_Rows_three_partition_strong_np_complete
-- name    : TetrisHard.Rows.three_partition_strong_np_complete
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T22:50:53.243801+00:00
-- url     : https://prove2.me/theorems/bbcdd9ba-47e8-4feb-a0f5-a83e2f2b01b8
-- title:
--   Theorem 3.1 — Strong NP-completeness of the source problem
-- statement:
--   Theorem 3.1 (Garey and Johnson [4]) 3-Partition is NP-complete in the strong sense.
--
--   The language contains exactly the unary encodings of valid indexed nonnegative 3-Partition instances admitting a partition of the indices into s parts of sum T. NP-completeness includes both membership in NP and reductions from every NP language over every finite nonempty alphabet. No positivity restriction on s or T is added.
--
--   Differences from the source:
--   - encoding: nonnegative input sequence and strong NP-completeness → indexed entries, zero-based indices and an explicit unary binary-alphabet language; reason: repeated integers retain separate indices; unary input expresses strong NP-completeness and includes empty instances
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Theorem 3.1, printed p. 7 = PDF p. 7, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_ThreePartition

namespace TetrisHard.Rows

theorem three_partition_strong_np_complete :
    CookPvsNP.NPComplete threePartitionLanguage := by sorry

end TetrisHard.Rows
