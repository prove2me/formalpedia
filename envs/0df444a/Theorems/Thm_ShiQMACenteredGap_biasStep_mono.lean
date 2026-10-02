-- Prove2me | Theorems.Thm_ShiQMACenteredGap_biasStep_mono
-- name    : ShiQMACenteredGap.biasStep_mono
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T23:41:36.577086+00:00
-- url     : https://prove2.me/theorems/25e8cff4-a6b9-4422-bb13-4dc188485769
-- title:
--   Majority amplification preserves centered bias order
-- statement:
--   The centered majority update is monotone on biases between zero and one half.
-- source:
--   https://github.com/shiy1022/qma-amplification-lean/blob/96c2a2d/proofs/AMPUNI-centered-gap.lean#L22-L31

import Definitions.Def_ShiQMACenteredGapGeneralSchedule

set_option autoImplicit false
set_option maxHeartbeats 2000000

open ShiQMACenteredGap ShiQMAErrorIteration ShiQMAConstructiveSchedule

theorem ShiQMACenteredGap.biasStep_mono {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e)
    (he : e ≤ 1 / 2) : biasStep d ≤ biasStep e := by sorry
