-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_expected
-- name    : ThreeSum.TernaryExtensionEncoding.arrayPolynomial_expected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:59.522242+00:00
-- url     : https://prove2.me/theorems/35a790cf-2b6f-4d9f-a40d-dbd2b1a515c6
-- title:
--   Ternary Extension Encoding: array Polynomial expected
-- statement:
--   The Ternary Extension Encoding construction uses the array Polynomial expected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProductCheckerExact.lean#L62-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProductCheckerExact.lean#L62-L77

import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryExtensionEncoding.arrayPolynomial_expected (d : ℕ) (h f r : ℕ → ℕ)
    (hr : ∀ k, d≤k → r k=0) :
    arrayPolynomial (p := p) (2*d) (LightPolynomialQuotientCheck.expected p d h f r)=
      arrayPolynomial d h*arrayPolynomial (d+1) f+arrayPolynomial d r := by sorry
