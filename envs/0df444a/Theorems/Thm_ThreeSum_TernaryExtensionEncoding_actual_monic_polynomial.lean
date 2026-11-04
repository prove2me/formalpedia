-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_actual_monic_polynomial
-- name    : ThreeSum.TernaryExtensionEncoding.actual_monic_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:21.52305+00:00
-- url     : https://prove2.me/theorems/9ae4810e-5750-4e95-8ffe-235a2808da85
-- title:
--   Ternary Extension Encoding: actual monic polynomial
-- statement:
--   The Ternary Extension Encoding construction uses the actual monic polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L38-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L38-L43

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.actual_monic_polynomial {d code : ℕ} (hc : code<p^d) :
    arrayPolynomial (p := p) (d+1) (fun k => (code+p^d)/p^k%p)=monicOfCode d code := by sorry
