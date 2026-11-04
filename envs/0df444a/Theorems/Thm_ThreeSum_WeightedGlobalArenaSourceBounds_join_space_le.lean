-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceBounds_join_space_le
-- name    : ThreeSum.WeightedGlobalArenaSourceBounds.join_space_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:03:59.642527+00:00
-- url     : https://prove2.me/theorems/6da58e2d-8098-4799-bcce-39b70339e843
-- title:
--   Weighted Global Arena Source Bounds: join space le
-- statement:
--   The Weighted Global Arena Source Bounds construction uses the join space le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L43-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L43-L61

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaSourceBounds.join_space_le {M NL NR U n W j : ℕ} (left right : ℕ→ℤ)
    (hl : NL≤n) (hr : NR≤W^j) :
    LightWantedSetup.space 0 M left right NL NR U 0 0≤
      10+n+2*W^j+4*M+U+2*n*W^j := by sorry
