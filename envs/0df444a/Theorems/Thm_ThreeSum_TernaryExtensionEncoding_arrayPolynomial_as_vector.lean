-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_as_vector
-- name    : ThreeSum.TernaryExtensionEncoding.arrayPolynomial_as_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:20:04.170753+00:00
-- url     : https://prove2.me/theorems/2b1285eb-089a-4124-b2f5-e418b94289bb
-- title:
--   Ternary Extension Encoding: array Polynomial as vector
-- statement:
--   The Ternary Extension Encoding construction uses the array Polynomial as vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L33-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryMonicCodes.lean#L33-L36

import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_TernaryExtensionProductSemantics
import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.arrayPolynomial_as_vector (n : ℕ) (a : ℕ → ℕ) :
    arrayPolynomial (p := p) n a=vectorPolynomial (fun i : Fin n => (a i.val : ZMod p)) := by sorry
