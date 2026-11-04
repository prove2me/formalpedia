-- Prove2me | Theorems.Thm_ThreeSum_LightSupportMark_bit_zero
-- name    : ThreeSum.LightSupportMark.bit_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:34.469333+00:00
-- url     : https://prove2.me/theorems/eccd9f9e-65f4-4cfc-8f17-a4deb549fc95
-- title:
--   Light Support Mark: bit zero
-- statement:
--   The Light Support Mark construction uses the bit zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L25-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSupportMark.lean#L25-L26

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightSupportMark
set_option autoImplicit false
open ThreeSum ThreeSum.LightSupportMark
open Light Finset

theorem ThreeSum.LightSupportMark.bit_zero (key valid : ℕ → ℕ) (r : ℕ) : bit key valid r 0 = 0 := by sorry
