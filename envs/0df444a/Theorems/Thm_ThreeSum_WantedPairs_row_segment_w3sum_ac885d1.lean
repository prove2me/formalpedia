-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_row_segment_w3sum_ac885d1
-- name    : ThreeSum.WantedPairs.row_segment_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:35.448999+00:00
-- url     : https://prove2.me/theorems/990e074b-8e91-474f-ab0f-943b0ef0afbc
-- title:
--   Wanted Pairs: row segment
-- statement:
--   The Wanted Pairs construction uses the row segment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L112-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedPairs.lean#L112-L137

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000

theorem ThreeSum.WantedPairs.row_segment_w3sum_ac885d1 {μ ν : ℕ → ℤ} {offsets flat NR M i dst previous : ℕ}
    {left right : ℕ → ℕ} (H : Stored μ right NR M offsets flat) (hr : ∀ j < NR, right j < M) (hi : left i < M)
    (hout :
      ∀ t < LightHistogram.count right (left i) NR,
        ν (dst + 2 * (previous + t)) = (i : ℤ) ∧
          ν (dst + 2 * (previous + t) + 1) = μ (flat + offset right NR (left i) + t)) :
    Seg ν (dst + 2 * previous) (cells (row μ offsets flat left i)) := by sorry
