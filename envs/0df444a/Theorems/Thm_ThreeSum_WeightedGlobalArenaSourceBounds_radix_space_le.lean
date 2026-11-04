-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceBounds_radix_space_le
-- name    : ThreeSum.WeightedGlobalArenaSourceBounds.radix_space_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:03:01.2874+00:00
-- url     : https://prove2.me/theorems/300efc03-22a4-48a0-9ea0-162bbc2024d2
-- title:
--   Weighted Global Arena Source Bounds: radix space le
-- statement:
--   The Weighted Global Arena Source Bounds construction uses the radix space le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L28-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceBounds.lean#L28-L41

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters LightTernarySourceHost WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaSourceBounds.radix_space_le {m W : ℕ} (hm : m≤W) (hW : 1≤W) (j : ℕ) :
    LightRadixKeys.space 0 m j≤(j+1)*(W^j+1) := by sorry
