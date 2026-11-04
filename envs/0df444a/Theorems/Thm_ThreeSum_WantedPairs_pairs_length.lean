-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_pairs_length
-- name    : ThreeSum.WantedPairs.pairs_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:00:53.2122+00:00
-- url     : https://prove2.me/theorems/3f027e0b-38d5-438c-beae-351bfd90f247
-- title:
--   Wanted Pairs: pairs length
-- statement:
--   The Wanted Pairs construction uses the pairs length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L54-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L54-L64

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem ThreeSum.WantedPairs.pairs_length {μ : ℕ → ℤ} {offsets flat NR M : ℕ} {left right : ℕ → ℕ}
    (H : Stored μ right NR M offsets flat) : ∀ n,
    (∀ i < n, left i < M) →
      (pairs μ offsets flat left n).length=count left right NR n := by sorry
