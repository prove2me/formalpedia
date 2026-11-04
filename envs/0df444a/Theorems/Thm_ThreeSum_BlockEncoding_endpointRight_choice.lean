-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_endpointRight_choice
-- name    : ThreeSum.BlockEncoding.endpointRight_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:16:56.950915+00:00
-- url     : https://prove2.me/theorems/fee56221-d6ba-4565-a48f-1fe2c44e9e4f
-- title:
--   Block Encoding: endpoint Right choice
-- statement:
--   The Block Encoding construction uses the endpoint Right choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L147-L157
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L147-L157

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.endpointRight_choice {h J : ℕ} (t : ChoiceTuple h J) (q : GlobalOutput h J)
    (hq : tupleOutput t = q) : endpointRight (outputOccurrences q) (rightSubset t) = tupleRight t := by sorry
