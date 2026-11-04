-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_rightWeights_cardinality
-- name    : ThreeSum.BlockEncoding.rightWeights_cardinality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:56.373307+00:00
-- url     : https://prove2.me/theorems/2d55401f-5f45-4362-8cf2-8a1ed97b2f07
-- title:
--   Block Encoding: right Weights cardinality
-- statement:
--   The Block Encoding construction uses the right Weights cardinality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L214-L220
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L214-L220

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

theorem ThreeSum.BlockEncoding.rightWeights_cardinality {h J : ℕ} (o : Occurrences h J) (P d : ℤ)
    (C : Finset γ) (c : γ → ℤ) (V : Finset (Coord J (512 * h)))
    (hV : (rightWeights o P d C c V : ℤ) ≠ 0) : V.card = J * h := by sorry
