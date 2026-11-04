-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_mem_pairs_w3sum_ac885d1
-- name    : ThreeSum.WantedPairs.mem_pairs_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:48.58002+00:00
-- url     : https://prove2.me/theorems/f22c4c22-3ca5-4cde-8f98-3f6971eed8bf
-- title:
--   Wanted Pairs: mem pairs
-- statement:
--   The Wanted Pairs construction uses the mem pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L66-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L66-L84

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem ThreeSum.WantedPairs.mem_pairs_w3sum_ac885d1 {μ : ℕ → ℤ} {offsets flat NR NL M i j : ℕ} {left right : ℕ → ℕ}
    (H : Stored μ right NR M offsets flat) (hl : ∀ a < NL, left a < M)
    (hr : ∀ b < NR, right b < M) :
    (i,j) ∈ pairs μ offsets flat left NL ↔ i < NL ∧ j < NR ∧ right j=left i := by sorry
