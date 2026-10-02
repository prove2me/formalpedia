-- Prove2me | Theorems.Thm_ShiQMACenteredGap_biasIter_mono
-- name    : ShiQMACenteredGap.biasIter_mono
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T23:54:05.539991+00:00
-- url     : https://prove2.me/theorems/c98443c9-4acd-4e5e-934c-76648475a87c
-- title:
--   Repeated majority amplification preserves centered bias order
-- statement:
--   For every round count, the iterated centered bias is monotone in an initial bias between zero and one half.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/96c2a2d/proofs/AMPUNI-general-gap-schedule.lean#L9-L15

import Definitions.Def_ShiQMACenteredGapGeneralSchedule
import Theorems.Thm_ShiQMACenteredGap_biasStep_mono
import Theorems.Thm_ShiQMACenteredGap_biasIter_bounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.biasIter_mono {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e)
    (he : e ≤ 1 / 2) (r : Nat) : biasIter d r ≤ biasIter e r := by sorry
