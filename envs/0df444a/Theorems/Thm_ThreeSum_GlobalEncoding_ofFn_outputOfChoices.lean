-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_ofFn_outputOfChoices
-- name    : ThreeSum.GlobalEncoding.ofFn_outputOfChoices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:45.309549+00:00
-- url     : https://prove2.me/theorems/050c6c41-ea7a-4128-97b2-49a941c69211
-- title:
--   Global Encoding: of Fn output Of Choices
-- statement:
--   The Global Encoding construction uses the of Fn output Of Choices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L264-L268
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L264-L268

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments

theorem ThreeSum.GlobalEncoding.ofFn_outputOfChoices {h J : ℕ} (xs : List (RetainedChoice h))
    (hlen : xs.length = J) :
    List.ofFn (outputOfChoices xs hlen) = xs.map blockOfChoice := by sorry
