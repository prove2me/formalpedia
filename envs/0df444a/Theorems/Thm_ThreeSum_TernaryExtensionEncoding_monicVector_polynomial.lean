-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicVector_polynomial
-- name    : ThreeSum.TernaryExtensionEncoding.monicVector_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:13.233671+00:00
-- url     : https://prove2.me/theorems/0f7da7bc-9825-4ad1-bee0-75c30fecff48
-- title:
--   Ternary Extension Encoding: monic Vector polynomial
-- statement:
--   The Ternary Extension Encoding construction uses the monic Vector polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L21-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L21-L25

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.monicVector_polynomial {d : ℕ} (a : Fin d → ZMod p) :
    vectorPolynomial (monicVector a)=monicCandidate a := by sorry
