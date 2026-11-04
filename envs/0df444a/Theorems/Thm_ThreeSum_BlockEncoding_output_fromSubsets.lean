-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_output_fromSubsets
-- name    : ThreeSum.BlockEncoding.output_fromSubsets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:54.883433+00:00
-- url     : https://prove2.me/theorems/69f76e0c-d004-4afa-b872-50fc0c6be308
-- title:
--   Block Encoding: output from Subsets
-- statement:
--   The Block Encoding construction uses the output from Subsets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L178-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L178-L188

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.output_fromSubsets {h J : ℕ} (q : GlobalOutput h J)
    (S V : Finset (Coord J (512 * h))) (hS : LeftAllowed (outputOccurrences q) S)
    (hV : RightAllowed (outputOccurrences q) V) (hd : Disjoint S V)
    (hu : S ∪ V = outputSubset q) :
    tupleOutput (fromSubsets (outputOccurrences q) S V hS hV hd) = q := by sorry
