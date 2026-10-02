-- Prove2me | Theorems.Thm_ShiQMACenteredGap_copies_generalGapRounds_le
-- name    : ShiQMACenteredGap.copies_generalGapRounds_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-02T00:41:01.103091+00:00
-- url     : https://prove2.me/theorems/ce842a7a-4c62-4036-a431-401b6ac07353
-- title:
--   General-gap QMA amplification has polynomial copy overhead
-- statement:
--   Three to the full general-gap round count is bounded by explicit polynomial factors for the gap and error target.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/96c2a2d/proofs/AMPUNI-general-gap-schedule.lean#L70-L80

import Definitions.Def_ShiQMACenteredGapGeneralSchedule
import Theorems.Thm_ShiQMAConstructiveSchedule_copies_rounds_le

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.copies_generalGapRounds_le (q p : Polynomial ℕ) (n : Nat) :
    3 ^ generalGapRounds q p n ≤
      (3 ^ (Nat.log 2 (q.eval 1 + 1) + q.natDegree + 4) *
        (n + 1) ^ (2 * q.natDegree)) ^ 3 *
      (3 ^ (Nat.log 2 (p.eval 1 + 1) + p.natDegree + 4) *
        (n + 1) ^ (2 * p.natDegree)) := by sorry
