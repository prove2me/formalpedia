-- Prove2me | Theorems.Thm_ThreeSum_LightPairSearch_goodCode_pair
-- name    : ThreeSum.LightPairSearch.goodCode_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:26.688201+00:00
-- url     : https://prove2.me/theorems/6ecf5477-a8eb-413f-8c18-5ae945154d5f
-- title:
--   Light Pair Search: good Code pair
-- statement:
--   The Light Pair Search construction uses the good Code pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PairFirst.lean#L56-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/PairFirst.lean#L56-L61

import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.DivMod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_PairFirst
set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
set_option maxHeartbeats 300000

theorem ThreeSum.LightPairSearch.goodCode_pair (q u v : ℕ) (hq : 0<q) (hv : v<q)
    (good : ℕ → ℕ → Prop) : goodCode q good (u*q+v) ↔ good u v := by sorry
