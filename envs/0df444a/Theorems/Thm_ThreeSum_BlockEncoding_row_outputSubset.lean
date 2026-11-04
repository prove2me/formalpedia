-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_row_outputSubset
-- name    : ThreeSum.BlockEncoding.row_outputSubset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:55.843576+00:00
-- url     : https://prove2.me/theorems/867bc7de-795c-4adf-99c5-ece42996c64b
-- title:
--   Block Encoding: row output Subset
-- statement:
--   The Block Encoding construction uses the row output Subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L39-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L39-L40

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.row_outputSubset {h J : ℕ} (q : GlobalOutput h J) (i : Fin J) :
    row (outputSubset q) i = (q i).2.val := by sorry
