-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_code_high_digit_zero
-- name    : ThreeSum.TernaryExtensionEncoding.code_high_digit_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:19:44.02111+00:00
-- url     : https://prove2.me/theorems/55cab872-ddf7-4d82-8f56-fe1692bb9f68
-- title:
--   Ternary Extension Encoding: code high digit zero
-- statement:
--   The Ternary Extension Encoding construction uses the code high digit zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoefficientCodes.lean#L60-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoefficientCodes.lean#L60-L64

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryExtensionEncoding.code_high_digit_zero {d code k : ℕ} (hc : code<p^d) (hk : d≤k) :
    code/p^k%p=0 := by sorry
