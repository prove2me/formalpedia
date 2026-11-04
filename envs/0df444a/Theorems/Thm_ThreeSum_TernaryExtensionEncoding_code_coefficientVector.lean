-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_code_coefficientVector
-- name    : ThreeSum.TernaryExtensionEncoding.code_coefficientVector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:19:47.11625+00:00
-- url     : https://prove2.me/theorems/f4c43743-c02d-4b82-a579-e254cbeb6888
-- title:
--   Ternary Extension Encoding: code coefficient Vector
-- statement:
--   The Ternary Extension Encoding construction uses the code coefficient Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoefficientCodes.lean#L54-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoefficientCodes.lean#L54-L58

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryExtensionEncoding.code_coefficientVector {d code : ℕ} (hc : code<p^d) :
    coefficientCode (coefficientVector (p := p) d code)=code := by sorry
