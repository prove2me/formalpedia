-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverInitResources_word_le_search
-- name    : ThreeSum.LightLocalCoverInitResources.word_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:38:07.901689+00:00
-- url     : https://prove2.me/theorems/a0853195-700e-4ad8-b9ca-2baec325c5fc
-- title:
--   Light Local Cover Init Resources: word le search
-- statement:
--   The Light Local Cover Init Resources construction uses the word le search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L85-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverInitResources.lean#L85-L87

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Theorems.Thm_ThreeSum_LightLocalCoverResources_word_le_search
import Theorems.Thm_ThreeSum_LocalParameterBounds_word_le_search

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000

theorem ThreeSum.LightLocalCoverInitResources.word_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalCoverInit.word (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 5000000 n := by sorry
