-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_eq_vector
-- name    : ThreeSum.TernaryExtensionEncoding.arrayPolynomial_eq_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:21.839044+00:00
-- url     : https://prove2.me/theorems/10a479e6-c0cc-495b-9680-ccfcd6815510
-- title:
--   Ternary Extension Encoding: array Polynomial eq vector
-- statement:
--   The Ternary Extension Encoding construction uses the array Polynomial eq vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionProductSemantics.lean#L46-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionProductSemantics.lean#L46-L53

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

theorem ThreeSum.TernaryExtensionEncoding.arrayPolynomial_eq_vector {d : ℕ} (a : Fin d → ZMod p) :
    arrayPolynomial d (fun i => if h : i<d then (a ⟨i,h⟩).val else 0)=
      vectorPolynomial a := by sorry
