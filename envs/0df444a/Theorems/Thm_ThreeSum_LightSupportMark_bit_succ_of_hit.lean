-- Prove2me | Theorems.Thm_ThreeSum_LightSupportMark_bit_succ_of_hit
-- name    : ThreeSum.LightSupportMark.bit_succ_of_hit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:36.740983+00:00
-- url     : https://prove2.me/theorems/1f2d2476-73c4-4ab5-aa1b-93615100de81
-- title:
--   Light Support Mark: bit succ of hit
-- statement:
--   The Light Support Mark construction uses the bit succ of hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L40-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L40-L42

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightSupportMark
set_option autoImplicit false
open ThreeSum ThreeSum.LightSupportMark
open Light Finset

theorem ThreeSum.LightSupportMark.bit_succ_of_hit (key valid : ℕ → ℕ) (r i : ℕ)
    (hv : valid i=1) (hk : key i=r) : bit key valid r (i+1) = 1 := by sorry
