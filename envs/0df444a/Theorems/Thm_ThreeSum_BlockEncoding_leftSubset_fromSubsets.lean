-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_fromSubsets
-- name    : ThreeSum.BlockEncoding.leftSubset_fromSubsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:25:13.739336+00:00
-- url     : https://prove2.me/theorems/60622d18-aa00-4da8-aac2-ba41671a76ea
-- title:
--   Block Encoding: left Subset from Subsets
-- statement:
--   The Block Encoding construction uses the left Subset from Subsets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L168-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L168-L171

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.leftSubset_fromSubsets {h J : ℕ} (o : Occurrences h J)
    (S V : Finset (Coord J (512 * h))) (hS : LeftAllowed o S)
    (hV : RightAllowed o V) (hd : Disjoint S V) :
    leftSubset (fromSubsets o S V hS hV hd) = S := by sorry
