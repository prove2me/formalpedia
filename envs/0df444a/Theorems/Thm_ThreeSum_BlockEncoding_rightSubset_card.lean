-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_rightSubset_card
-- name    : ThreeSum.BlockEncoding.rightSubset_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:52.528868+00:00
-- url     : https://prove2.me/theorems/eb3ed585-3626-439e-84e2-0147bfdfbd5f
-- title:
--   Block Encoding: right Subset card
-- statement:
--   The Block Encoding construction uses the right Subset card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L45-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L45-L47

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.rightSubset_card {h J : ℕ} (t : ChoiceTuple h J) :
    (rightSubset t).card = J * h := by sorry
