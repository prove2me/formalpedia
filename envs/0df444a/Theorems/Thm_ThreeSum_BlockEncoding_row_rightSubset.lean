-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_row_rightSubset
-- name    : ThreeSum.BlockEncoding.row_rightSubset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:24:58.943799+00:00
-- url     : https://prove2.me/theorems/d8f676e3-d8e4-452b-8766-213076f23b08
-- title:
--   Block Encoding: row right Subset
-- statement:
--   The Block Encoding construction uses the row right Subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L36-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L36-L37

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.row_rightSubset {h J : ℕ} (t : ChoiceTuple h J) (i : Fin J) :
    row (rightSubset t) i = (edge (t i)).val.2 := by sorry
