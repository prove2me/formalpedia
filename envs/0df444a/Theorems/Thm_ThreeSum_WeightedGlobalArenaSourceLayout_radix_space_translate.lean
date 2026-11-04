-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceLayout_radix_space_translate
-- name    : ThreeSum.WeightedGlobalArenaSourceLayout.radix_space_translate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:49:45.944552+00:00
-- url     : https://prove2.me/theorems/a7061af3-ae54-4c3e-8e6d-eed2fe98d4b9
-- title:
--   Weighted Global Arena Source Layout: radix space translate
-- statement:
--   The Weighted Global Arena Source Layout construction uses the radix space translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceLayout.lean#L27-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceLayout.lean#L27-L30

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceLayout
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaSourceLayout
open WeightedGlobalArenaLayout TernarySourceExecutionFactory LightTernarySourceHost

theorem ThreeSum.WeightedGlobalArenaSourceLayout.radix_space_translate (dst m j : ℕ) :
    LightRadixKeys.space dst m j=dst+LightRadixKeys.space 0 m j := by sorry
