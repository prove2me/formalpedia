-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_product_valid_coefficients
-- name    : ThreeSum.TernaryExtensionEncoding.product_valid_coefficients
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:14.394407+00:00
-- url     : https://prove2.me/theorems/1497cec1-702e-4f7b-b68e-e976ef1f6313
-- title:
--   Ternary Extension Encoding: product valid coefficients
-- statement:
--   The Ternary Extension Encoding construction uses the product valid coefficients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionProductSemantics.lean#L55-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionProductSemantics.lean#L55-L63

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryExtensionEncoding.product_valid_coefficients (a b expected : ℕ → ℕ) (n m len : ℕ)
    (h : LightPolynomialProductCheck.Valid p a b expected n m len) :
    ∀ k<len, (arrayPolynomial (p := p) n a*arrayPolynomial m b).coeff k=
      (expected k : ZMod p) := by sorry
