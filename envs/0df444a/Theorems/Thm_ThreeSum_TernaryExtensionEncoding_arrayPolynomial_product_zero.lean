-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_product_zero
-- name    : ThreeSum.TernaryExtensionEncoding.arrayPolynomial_product_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:20:35.825715+00:00
-- url     : https://prove2.me/theorems/859dab1c-45a6-40f0-811d-1e6e6e7c9b8d
-- title:
--   Ternary Extension Encoding: array Polynomial product zero
-- statement:
--   The Ternary Extension Encoding construction uses the array Polynomial product zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProductCheckerExact.lean#L17-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProductCheckerExact.lean#L17-L31

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

theorem ThreeSum.TernaryExtensionEncoding.arrayPolynomial_product_zero (n m k : ℕ) (a b : ℕ → ℕ)
    (hk : n+m-1≤k) :
    (arrayPolynomial (p := p) n a*arrayPolynomial m b).coeff k=0 := by sorry
