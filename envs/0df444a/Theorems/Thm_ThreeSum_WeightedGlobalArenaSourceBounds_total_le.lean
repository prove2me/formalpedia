-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceBounds_total_le
-- name    : ThreeSum.WeightedGlobalArenaSourceBounds.total_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:03:55.524876+00:00
-- url     : https://prove2.me/theorems/6fe30042-080b-43c9-9560-e2ac8823ab3c
-- title:
--   Weighted Global Arena Source Bounds: total le
-- statement:
--   The literal join can retain every original-position/dictionary-tuple
--   pair. This bound retains all repeated physical representations.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L18-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L18-L26

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaSourceBounds.total_le (M NL NR : ℕ) (left right : ℕ→ℤ) :
    WantedResidueKeys.total M left right NL NR 0≤NL*NR := by sorry
