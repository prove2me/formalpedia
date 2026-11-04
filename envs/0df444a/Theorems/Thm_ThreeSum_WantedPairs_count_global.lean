-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_count_global
-- name    : ThreeSum.WantedPairs.count_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:31.839624+00:00
-- url     : https://prove2.me/theorems/e2aee82e-2af8-48a2-b37e-efd698808f69
-- title:
--   Wanted Pairs: count global
-- statement:
--   The Wanted Pairs construction uses the count global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L160-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L160-L171

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem ThreeSum.WantedPairs.count_global (M : ℕ) (hM : 0 < M) (as : List ℤ) (h J : ℕ) (d : ℤ) :
    count (fun i => LightResidues.residue M 1 (as.getD i 0+d))
      (fun j => LightResidues.residue M 1 ((GlobalKeyEnumeration.globalKeys h J).getD j 0))
      (GlobalKeyEnumeration.globalKeys h J).length as.length =
      GlobalKeyOffset.wantedCount M as h J d := by sorry
