-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_rightAllowed_choice
-- name    : ThreeSum.BlockEncoding.rightAllowed_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:55.005019+00:00
-- url     : https://prove2.me/theorems/57d35b35-94f7-4e9e-9743-2f51e4a71f8e
-- title:
--   Block Encoding: right Allowed choice
-- statement:
--   The Block Encoding construction uses the right Allowed choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L127-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L127-L133

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.rightAllowed_choice {h J : ℕ} (t : ChoiceTuple h J) (q : GlobalOutput h J)
    (hq : tupleOutput t = q) : RightAllowed (outputOccurrences q) (rightSubset t) := by sorry
