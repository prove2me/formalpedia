-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_rawHash_cast
-- name    : ThreeSum.GlobalEncoding.rawHash_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:39.141751+00:00
-- url     : https://prove2.me/theorems/bc096d5a-c0ca-4847-8585-3afcac7f6974
-- title:
--   Global Encoding: raw Hash cast
-- statement:
--   The Global Encoding construction uses the raw Hash cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L68-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L68-L70

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

theorem ThreeSum.GlobalEncoding.rawHash_cast {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (rawHash w s : LocalField h) = HashFamily.hashValue w s := by sorry
