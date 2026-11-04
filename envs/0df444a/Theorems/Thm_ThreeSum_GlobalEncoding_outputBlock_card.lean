-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_outputBlock_card
-- name    : ThreeSum.GlobalEncoding.outputBlock_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:44.959223+00:00
-- url     : https://prove2.me/theorems/11b441b7-26d8-49fc-b483-e7a48b8ebcc2
-- title:
--   Global Encoding: output Block card
-- statement:
--   The Global Encoding construction uses the output Block card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L234-L237
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L234-L237

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

theorem ThreeSum.GlobalEncoding.outputBlock_card (h : ℕ) :
    Fintype.card (OutputBlock h) = scheduleSize h * outputCount (512 * h) h := by sorry
