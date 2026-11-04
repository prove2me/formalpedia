-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_union_right
-- name    : ThreeSum.BlockEncoding.leftSubset_union_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:26:58.308139+00:00
-- url     : https://prove2.me/theorems/de006d20-3cb3-4a78-971d-6e0736317287
-- title:
--   Block Encoding: left Subset union right
-- statement:
--   The Block Encoding construction uses the left Subset union right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L60-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L60-L64

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.leftSubset_union_right {h J : ℕ} (t : ChoiceTuple h J) :
    leftSubset t ∪ rightSubset t = outputSubset (tupleOutput t) := by sorry
