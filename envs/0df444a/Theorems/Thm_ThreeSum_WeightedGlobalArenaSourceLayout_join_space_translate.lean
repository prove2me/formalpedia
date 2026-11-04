-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceLayout_join_space_translate
-- name    : ThreeSum.WeightedGlobalArenaSourceLayout.join_space_translate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:58:36.458672+00:00
-- url     : https://prove2.me/theorems/793a9a7c-cb65-49cd-a054-7206eaae4b5f
-- title:
--   Weighted Global Arena Source Layout: join space translate
-- statement:
--   The Weighted Global Arena Source Layout construction uses the join space translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceLayout.lean#L32-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceLayout.lean#L32-L42

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceLayout
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaSourceLayout
open WeightedGlobalArenaLayout TernarySourceExecutionFactory LightTernarySourceHost

theorem ThreeSum.WeightedGlobalArenaSourceLayout.join_space_translate (free M NL NR U : ℕ) (input dictionary : ℕ→ℤ) :
    LightWantedSetup.space free M input dictionary NL NR U 0 0=
      free+LightWantedSetup.space 0 M input dictionary NL NR U 0 0 := by sorry
