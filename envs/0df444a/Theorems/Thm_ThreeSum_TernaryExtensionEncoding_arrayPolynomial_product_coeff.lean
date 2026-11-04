-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_product_coeff
-- name    : ThreeSum.TernaryExtensionEncoding.arrayPolynomial_product_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:22.527502+00:00
-- url     : https://prove2.me/theorems/379f2663-4e84-404d-8312-8fffdce7ad9e
-- title:
--   Ternary Extension Encoding: array Polynomial product coeff
-- statement:
--   The Ternary Extension Encoding construction uses the array Polynomial product coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionProductSemantics.lean#L21-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionProductSemantics.lean#L21-L44

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

theorem ThreeSum.TernaryExtensionEncoding.arrayPolynomial_product_coeff (n m k : ℕ) (a b : ℕ → ℕ) :
    (arrayPolynomial (p := p) n a*arrayPolynomial m b).coeff k=
      (LightPolynomialCoefficient.coefficient p a b n m k : ZMod p) := by sorry
