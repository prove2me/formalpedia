-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_vectorPolynomial_degree_lt
-- name    : ThreeSum.TernaryExtensionEncoding.vectorPolynomial_degree_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:02:50.450007+00:00
-- url     : https://prove2.me/theorems/50f19c10-0318-4393-8943-044b4e7ccd22
-- title:
--   Ternary Extension Encoding: vector Polynomial degree lt
-- statement:
--   The Ternary Extension Encoding construction uses the vector Polynomial degree lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L18-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L18-L22

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.vectorPolynomial_degree_lt {d : ℕ} (a : Fin d → ZMod p) :
    (vectorPolynomial a).degree < d := by sorry
