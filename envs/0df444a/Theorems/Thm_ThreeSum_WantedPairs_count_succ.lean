-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_count_succ
-- name    : ThreeSum.WantedPairs.count_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:00:16.650282+00:00
-- url     : https://prove2.me/theorems/be329bfc-c4bf-4c9a-988d-ae155e71a626
-- title:
--   Wanted Pairs: count succ
-- statement:
--   The Wanted Pairs construction uses the count succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L27-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L27-L29

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Theorems.Thm_ThreeSum_LightHistogram_count_succ

set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem ThreeSum.WantedPairs.count_succ (left right : ℕ → ℕ) (NR n : ℕ) :
    count left right NR (n+1)=count left right NR n+LightHistogram.count right (left n) NR := by sorry
