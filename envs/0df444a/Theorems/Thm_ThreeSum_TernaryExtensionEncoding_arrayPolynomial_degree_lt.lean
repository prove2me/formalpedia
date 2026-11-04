-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_degree_lt
-- name    : ThreeSum.TernaryExtensionEncoding.arrayPolynomial_degree_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:35.973651+00:00
-- url     : https://prove2.me/theorems/14567198-5ceb-406a-b6a2-49c2c38ef1fb
-- title:
--   Ternary Extension Encoding: array Polynomial degree lt
-- statement:
--   The Ternary Extension Encoding construction uses the array Polynomial degree lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProductCheckerExact.lean#L11-L15
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProductCheckerExact.lean#L11-L15

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

theorem ThreeSum.TernaryExtensionEncoding.arrayPolynomial_degree_lt (n : ℕ) (a : ℕ → ℕ) :
    (arrayPolynomial (p := p) n a).degree < n := by sorry
