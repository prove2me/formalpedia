-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_eq_sdiff
-- name    : ThreeSum.BlockEncoding.rightSubset_eq_sdiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:27:11.859576+00:00
-- url     : https://prove2.me/theorems/bdc2eba1-0a68-46cf-b517-1cd3b962a1a4
-- title:
--   Block Encoding: right Subset eq sdiff
-- statement:
--   The Block Encoding construction uses the right Subset eq sdiff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L66-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L66-L72

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.rightSubset_eq_sdiff {h J : ℕ} (t : ChoiceTuple h J) :
    rightSubset t = outputSubset (tupleOutput t) \ leftSubset t := by sorry
