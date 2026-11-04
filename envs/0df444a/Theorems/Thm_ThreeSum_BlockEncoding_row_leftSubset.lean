-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_row_leftSubset
-- name    : ThreeSum.BlockEncoding.row_leftSubset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:25:13.630953+00:00
-- url     : https://prove2.me/theorems/63124dfb-547a-4843-a7d2-97a1c46d881b
-- title:
--   Block Encoding: row left Subset
-- statement:
--   The Block Encoding construction uses the row left Subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L33-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L33-L34

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.row_leftSubset {h J : ℕ} (t : ChoiceTuple h J) (i : Fin J) :
    row (leftSubset t) i = (edge (t i)).val.1 := by sorry
