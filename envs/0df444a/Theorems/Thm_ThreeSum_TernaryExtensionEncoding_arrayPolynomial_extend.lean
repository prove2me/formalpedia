-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_extend
-- name    : ThreeSum.TernaryExtensionEncoding.arrayPolynomial_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:44.345548+00:00
-- url     : https://prove2.me/theorems/aac7e35b-5f5c-4913-89c0-2c1f76e9e035
-- title:
--   Ternary Extension Encoding: array Polynomial extend
-- statement:
--   The Ternary Extension Encoding construction uses the array Polynomial extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProductCheckerExact.lean#L51-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProductCheckerExact.lean#L51-L60

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

theorem ThreeSum.TernaryExtensionEncoding.arrayPolynomial_extend (n len : ℕ) (a : ℕ → ℕ) (hn : n≤len)
    (hz : ∀ k, n≤k → a k=0) :
    arrayPolynomial (p := p) len a=arrayPolynomial n a := by sorry
