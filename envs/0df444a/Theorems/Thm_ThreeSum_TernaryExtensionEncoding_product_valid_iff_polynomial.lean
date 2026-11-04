-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_product_valid_iff_polynomial
-- name    : ThreeSum.TernaryExtensionEncoding.product_valid_iff_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:20:13.280982+00:00
-- url     : https://prove2.me/theorems/b1cb33e5-058b-4088-87f7-e2464b9476ce
-- title:
--   Ternary Extension Encoding: product valid iff polynomial
-- statement:
--   The Ternary Extension Encoding construction uses the product valid iff polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProductCheckerExact.lean#L33-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryProductCheckerExact.lean#L33-L49

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

theorem ThreeSum.TernaryExtensionEncoding.product_valid_iff_polynomial (a b expected : ℕ → ℕ) (n m len : ℕ)
    (hlen : n+m-1≤len) (hb : ∀ k<len, expected k<p) :
    LightPolynomialProductCheck.Valid p a b expected n m len ↔
      arrayPolynomial n a*arrayPolynomial m b=arrayPolynomial (p := p) len expected := by sorry
