-- Prove2me | Theorems.Thm_ThreeSum_BlockForced_forced_right_completion
-- name    : ThreeSum.BlockForced.forced_right_completion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:14.877726+00:00
-- url     : https://prove2.me/theorems/794eb0d6-135b-487d-a0cd-46b8d7502d24
-- title:
--   Block Forced: forced right completion
-- statement:
--   The Block Forced construction uses the forced right completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L152-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockForced.lean#L152-L163

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
set_option autoImplicit false
open ThreeSum ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding

theorem ThreeSum.BlockForced.forced_right_completion {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h)))
    (hu : ∀ i ∈ I, u i ⊆ outputRows q i) (t : ChoiceTuple h J)
    (ht : t ∈ completedTuples q I u) :
    prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ residual I t) =
      rightSubset t := by sorry
