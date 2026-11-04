-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_pairs_nodup_w3sum_ac885d1
-- name    : ThreeSum.WantedPairs.pairs_nodup_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:25.924378+00:00
-- url     : https://prove2.me/theorems/0298252f-d592-48d9-872c-a553ce72aa0e
-- title:
--   Wanted Pairs: pairs nodup
-- statement:
--   The Wanted Pairs construction uses the pairs nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L86-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L86-L100

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem ThreeSum.WantedPairs.pairs_nodup_w3sum_ac885d1 {μ : ℕ → ℤ} {offsets flat NR NL M : ℕ} {left right : ℕ → ℕ}
    (H : Stored μ right NR M offsets flat) (hl : ∀ a < NL, left a < M)
    (hr : ∀ b < NR, right b < M) : (pairs μ offsets flat left NL).Nodup := by sorry
