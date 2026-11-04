-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_vectorPolynomial_coeff
-- name    : ThreeSum.TernaryExtensionEncoding.vectorPolynomial_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:06:47.84287+00:00
-- url     : https://prove2.me/theorems/c933860d-481a-494d-bfc7-5cc4380334cb
-- title:
--   Ternary Extension Encoding: vector Polynomial coeff
-- statement:
--   The Ternary Extension Encoding construction uses the vector Polynomial coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L24-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L24-L27

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.vectorPolynomial_coeff {d : ℕ} (a : Fin d → ZMod p) (i : Fin d) :
    (vectorPolynomial a).coeff i.val=a i := by sorry
