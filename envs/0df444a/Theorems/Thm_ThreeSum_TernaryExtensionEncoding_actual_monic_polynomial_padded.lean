-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_actual_monic_polynomial_padded
-- name    : ThreeSum.TernaryExtensionEncoding.actual_monic_polynomial_padded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:20.828328+00:00
-- url     : https://prove2.me/theorems/1fc70306-25df-43c3-987e-fa64b2b0b7d3
-- title:
--   Ternary Extension Encoding: actual monic polynomial padded
-- statement:
--   The Ternary Extension Encoding construction uses the actual monic polynomial padded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L27-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L27-L32

import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryExtensionEncoding.actual_monic_polynomial_padded {d code : ℕ} (hd : 0<d) (hc : code<p^d) :
    arrayPolynomial (p := p) (2*d) (codeDigits (p := p) (code+p^d))=monicOfCode d code := by sorry
