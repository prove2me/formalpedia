-- Prove2me | Theorems.Thm_ShiQMACenteredGap_biasStep_ge
-- name    : ShiQMACenteredGap.biasStep_ge
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-02T01:24:42.012369+00:00
-- url     : https://prove2.me/theorems/056fa939-7481-47e7-a3d2-d9f1ee301042
-- title:
--   A centered majority round never decreases valid bias
-- statement:
--   On the nonnegative half interval, one majority update is at least the original bias.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/71839d3/proofs/AMPUNI-gap-dominating-schedule.lean#L37-L41

import Definitions.Def_ShiQMACenteredGapDominatingSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.biasStep_ge {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1 / 2) : d ≤ biasStep d := by sorry
