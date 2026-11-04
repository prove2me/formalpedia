-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_count_zero
-- name    : ThreeSum.WantedPairs.count_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:00:02.708976+00:00
-- url     : https://prove2.me/theorems/6ba960d7-de3f-4430-a0db-6f9f99784e84
-- title:
--   Wanted Pairs: count zero
-- statement:
--   The Wanted Pairs construction uses the count zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L24-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L24-L25

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero


set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem ThreeSum.WantedPairs.count_zero (left right : ℕ → ℕ) (NR : ℕ) : count left right NR 0=0 := by sorry
