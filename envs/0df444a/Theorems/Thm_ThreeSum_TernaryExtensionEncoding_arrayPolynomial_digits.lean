-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_digits
-- name    : ThreeSum.TernaryExtensionEncoding.arrayPolynomial_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:22:24.722592+00:00
-- url     : https://prove2.me/theorems/fceb367c-adc4-41a4-a87d-bce079b83158
-- title:
--   Ternary Extension Encoding: array Polynomial digits
-- statement:
--   The Ternary Extension Encoding construction uses the array Polynomial digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L16-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCheckerSemantics.lean#L16-L19

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

theorem ThreeSum.TernaryExtensionEncoding.arrayPolynomial_digits (d code : ℕ) :
    arrayPolynomial (p := p) d (codeDigits (p := p) code)=vectorPolynomial (coefficientVector d code) := by sorry
