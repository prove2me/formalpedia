-- Prove2me | Theorems.Thm_ThreeSum_LightSupportMark_bit_succ_of_not
-- name    : ThreeSum.LightSupportMark.bit_succ_of_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:44.180994+00:00
-- url     : https://prove2.me/theorems/74e4ffca-edae-455a-be8f-efec73a018b0
-- title:
--   Light Support Mark: bit succ of not
-- statement:
--   The Light Support Mark construction uses the bit succ of not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L44-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L44-L55

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightSupportMark
set_option autoImplicit false
open ThreeSum ThreeSum.LightSupportMark
open Light Finset

theorem ThreeSum.LightSupportMark.bit_succ_of_not (key valid : ℕ → ℕ) (r i : ℕ)
    (h : ¬(valid i=1 ∧ key i=r)) : bit key valid r (i+1) = bit key valid r i := by sorry
