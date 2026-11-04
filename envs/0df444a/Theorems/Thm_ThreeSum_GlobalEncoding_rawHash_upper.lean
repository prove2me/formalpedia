-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_rawHash_upper
-- name    : ThreeSum.GlobalEncoding.rawHash_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:26.108394+00:00
-- url     : https://prove2.me/theorems/1cac51e9-4e52-47be-bd03-038bce20ebd3
-- title:
--   Global Encoding: raw Hash upper
-- statement:
--   The Global Encoding construction uses the raw Hash upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L75-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L75-L85

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

theorem ThreeSum.GlobalEncoding.rawHash_upper {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    rawHash w s ≤ (L : ℤ) * (localPrime h - 1) := by sorry
