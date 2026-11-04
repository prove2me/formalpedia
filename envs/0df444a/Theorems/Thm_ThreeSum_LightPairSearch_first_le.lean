-- Prove2me | Theorems.Thm_ThreeSum_LightPairSearch_first_le
-- name    : ThreeSum.LightPairSearch.first_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:25:44.801999+00:00
-- url     : https://prove2.me/theorems/d2dedfe3-906d-4b55-a116-d1c4072f4d40
-- title:
--   Light Pair Search: first le
-- statement:
--   The Light Pair Search construction uses the first le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PairFirst.lean#L10-L14
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PairFirst.lean#L10-L14

import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.DivMod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_PairFirst
set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
set_option maxHeartbeats 300000

theorem ThreeSum.LightPairSearch.first_le (good : ℕ → Prop) [DecidablePred good] : ∀ k, first good k≤k := by sorry
