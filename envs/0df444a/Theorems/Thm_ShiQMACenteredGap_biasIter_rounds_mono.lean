-- Prove2me | Theorems.Thm_ShiQMACenteredGap_biasIter_rounds_mono
-- name    : ShiQMACenteredGap.biasIter_rounds_mono
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-02T01:32:41.681484+00:00
-- url     : https://prove2.me/theorems/b2523487-d812-47ba-b66b-77cc9239c752
-- title:
--   Additional majority rounds never decrease centered bias
-- statement:
--   For an initial bias in the valid half interval, the iterated bias is monotone in the number of rounds.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/71839d3/proofs/AMPUNI-gap-dominating-schedule.lean#L43-L47

import Definitions.Def_ShiQMACenteredGapDominatingSchedule
import Theorems.Thm_ShiQMACenteredGap_biasStep_ge
import Theorems.Thm_ShiQMACenteredGap_biasIter_bounds

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.biasIter_rounds_mono {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2)
    {r s : Nat} (hrs : r ≤ s) : biasIter d r ≤ biasIter d s := by sorry
