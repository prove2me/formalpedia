-- Prove2me | Theorems.Thm_ThreeSum_BlockForced_completed_bucket_sum_w3sum_ac885d1
-- name    : ThreeSum.BlockForced.completed_bucket_sum_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:13:36.559196+00:00
-- url     : https://prove2.me/theorems/4b29aecd-dac6-4842-9cb9-c68ed97cbbec
-- title:
--   Block Forced: completed bucket sum
-- statement:
--   The Block Forced construction uses the completed bucket sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L218-L251
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L218-L251

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
set_option autoImplicit false
open ThreeSum ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.BlockForced.completed_bucket_sum_w3sum_ac885d1 {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) (hu : ∀ i ∈ I, u i ⊆ outputRows q i) :
    (∑ t ∈ completedTuples q I u, leftBucket P B b t * rightBucket P d C c t) =
      ∑ x ∈ (remaining I (outputRows q)).powerset,
        leftWeights (outputOccurrences q) P B b (prefixLeft I u ∪ x) *
        rightWeights (outputOccurrences q) P d C c
          (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x)) := by sorry
