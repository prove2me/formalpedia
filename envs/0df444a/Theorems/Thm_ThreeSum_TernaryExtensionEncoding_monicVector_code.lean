-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicVector_code
-- name    : ThreeSum.TernaryExtensionEncoding.monicVector_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:13.692128+00:00
-- url     : https://prove2.me/theorems/8b40b83c-dc7c-4819-b8cf-e7e64bf7a092
-- title:
--   Ternary Extension Encoding: monic Vector code
-- statement:
--   The Ternary Extension Encoding construction uses the monic Vector code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L14-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L14-L19

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.monicVector_code {d : ℕ} (a : Fin d → ZMod p) :
    coefficientCode (monicVector a)=coefficientCode a+p^d := by sorry
