-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_fromSubsets
-- name    : ThreeSum.BlockEncoding.rightSubset_fromSubsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:25:17.630208+00:00
-- url     : https://prove2.me/theorems/76b90e54-b943-47ad-92db-76e6ce5e5c98
-- title:
--   Block Encoding: right Subset from Subsets
-- statement:
--   The Block Encoding construction uses the right Subset from Subsets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L173-L176
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L173-L176

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.rightSubset_fromSubsets {h J : ℕ} (o : Occurrences h J)
    (S V : Finset (Coord J (512 * h))) (hS : LeftAllowed o S)
    (hV : RightAllowed o V) (hd : Disjoint S V) :
    rightSubset (fromSubsets o S V hS hV hd) = V := by sorry
