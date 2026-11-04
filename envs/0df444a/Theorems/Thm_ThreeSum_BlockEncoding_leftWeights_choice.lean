-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_leftWeights_choice
-- name    : ThreeSum.BlockEncoding.leftWeights_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:53.94229+00:00
-- url     : https://prove2.me/theorems/2234ddc6-50e5-4ab9-ab23-b34e2d61e809
-- title:
--   Block Encoding: left Weights choice
-- statement:
--   The Block Encoding construction uses the left Weights choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L222-L226
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L222-L226

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.BlockEncoding.leftWeights_choice {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    (t : ChoiceTuple h J) (q : GlobalOutput h J) (hq : tupleOutput t = q) :
    leftWeights (outputOccurrences q) P B b (leftSubset t) = leftBucket P B b t := by sorry
