-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_rightWeights_choice
-- name    : ThreeSum.BlockEncoding.rightWeights_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:57.890048+00:00
-- url     : https://prove2.me/theorems/f9159d97-83c5-4363-a0f9-3447b185df59
-- title:
--   Block Encoding: right Weights choice
-- statement:
--   The Block Encoding construction uses the right Weights choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L228-L232
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L228-L232

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

theorem ThreeSum.BlockEncoding.rightWeights_choice {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (t : ChoiceTuple h J) (q : GlobalOutput h J) (hq : tupleOutput t = q) :
    rightWeights (outputOccurrences q) P d C c (rightSubset t) = rightBucket P d C c t := by sorry
