-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_endpointLeft_choice
-- name    : ThreeSum.BlockEncoding.endpointLeft_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:53.991709+00:00
-- url     : https://prove2.me/theorems/f29da6dc-e6f4-488a-b43d-8bd1d50cd058
-- title:
--   Block Encoding: endpoint Left choice
-- statement:
--   The Block Encoding construction uses the endpoint Left choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L135-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L135-L145

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.endpointLeft_choice {h J : ℕ} (t : ChoiceTuple h J) (q : GlobalOutput h J)
    (hq : tupleOutput t = q) : endpointLeft (outputOccurrences q) (leftSubset t) = tupleLeft t := by sorry
