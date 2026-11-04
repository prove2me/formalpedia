-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_rawHash_difference
-- name    : ThreeSum.GlobalEncoding.rawHash_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:30.921373+00:00
-- url     : https://prove2.me/theorems/294568a6-7f7f-4417-ab74-ffedce258b0a
-- title:
--   Global Encoding: raw Hash difference
-- statement:
--   The Global Encoding construction uses the raw Hash difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L209-L218
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L209-L218

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

theorem ThreeSum.GlobalEncoding.rawHash_difference {h L k : ℕ} (w : Weight L (LocalField h))
    (e : Edge L k) :
    rawHash w (right e) - rawHash w (left e) = rawOutput w (output e) := by sorry
