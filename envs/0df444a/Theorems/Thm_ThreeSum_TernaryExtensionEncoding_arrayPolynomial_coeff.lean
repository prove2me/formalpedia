-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_coeff
-- name    : ThreeSum.TernaryExtensionEncoding.arrayPolynomial_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:11.464968+00:00
-- url     : https://prove2.me/theorems/acae799d-e37c-48a8-aa82-2537a193cf5a
-- title:
--   Ternary Extension Encoding: array Polynomial coeff
-- statement:
--   The Ternary Extension Encoding construction uses the array Polynomial coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionProductSemantics.lean#L17-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionProductSemantics.lean#L17-L19

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

theorem ThreeSum.TernaryExtensionEncoding.arrayPolynomial_coeff (n k : ℕ) (a : ℕ → ℕ) :
    (arrayPolynomial (p := p) n a).coeff k=if k<n then (a k : ZMod p) else 0 := by sorry
