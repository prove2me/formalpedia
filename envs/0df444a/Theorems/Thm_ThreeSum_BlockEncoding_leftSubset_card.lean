-- Prove2me | Theorems.Thm_ThreeSum_BlockEncoding_leftSubset_card
-- name    : ThreeSum.BlockEncoding.leftSubset_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:50.057951+00:00
-- url     : https://prove2.me/theorems/3bb8e782-ca8a-4eb0-ad6b-e9f84c86fb07
-- title:
--   Block Encoding: left Subset card
-- statement:
--   The Block Encoding construction uses the left Subset card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L42-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockEncoding.lean#L42-L43

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

theorem ThreeSum.BlockEncoding.leftSubset_card {h J : ℕ} (t : ChoiceTuple h J) :
    (leftSubset t).card = J * h := by sorry
