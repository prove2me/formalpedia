-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_decode_monic_code
-- name    : ThreeSum.TernaryExtensionEncoding.decode_monic_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:17.014666+00:00
-- url     : https://prove2.me/theorems/2a727119-d6cf-47fb-a7be-b3538f6e76f3
-- title:
--   Ternary Extension Encoding: decode monic code
-- statement:
--   The Ternary Extension Encoding construction uses the decode monic code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L27-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L27-L31

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.decode_monic_code {d code : ℕ} (hc : code<p^d) :
    coefficientVector (p := p) (d+1) (code+p^d)=monicVector (coefficientVector d code) := by sorry
