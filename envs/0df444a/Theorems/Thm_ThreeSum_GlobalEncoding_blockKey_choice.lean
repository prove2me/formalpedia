-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_blockKey_choice
-- name    : ThreeSum.GlobalEncoding.blockKey_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:42.035027+00:00
-- url     : https://prove2.me/theorems/63433a12-9e98-445a-8022-10b5bcea18e1
-- title:
--   Global Encoding: block Key choice
-- statement:
--   The Global Encoding construction uses the block Key choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L230-L232
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L230-L232

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

theorem ThreeSum.GlobalEncoding.blockKey_choice {h : ℕ} (c : RetainedChoice h) :
    blockKey (blockOfChoice c) = rawRight c - rawLeft c := by sorry
