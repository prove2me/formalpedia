-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_dvd_sub_rawHash_iff
-- name    : ThreeSum.GlobalEncoding.dvd_sub_rawHash_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:30.591256+00:00
-- url     : https://prove2.me/theorems/7e42697a-48d9-484a-b3f8-de81a242961c
-- title:
--   Global Encoding: dvd sub raw Hash iff
-- statement:
--   The Global Encoding construction uses the dvd sub raw Hash iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L87-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L87-L92

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

theorem ThreeSum.GlobalEncoding.dvd_sub_rawHash_iff {h L : ℕ} (a : ℤ)
    (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (localPrime h : ℤ) ∣ a - rawHash w s ↔
      HashFamily.hashValue w s = (a : LocalField h) := by sorry
