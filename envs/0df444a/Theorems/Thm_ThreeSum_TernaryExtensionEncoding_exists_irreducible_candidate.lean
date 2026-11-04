-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_exists_irreducible_candidate
-- name    : ThreeSum.TernaryExtensionEncoding.exists_irreducible_candidate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:33.369033+00:00
-- url     : https://prove2.me/theorems/eabbc6bb-9143-4e6a-b0b8-6b9fcd0fb740
-- title:
--   Ternary Extension Encoding: exists irreducible candidate
-- statement:
--   The Ternary Extension Encoding construction uses the exists irreducible candidate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L70-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L70-L75

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.exists_irreducible_candidate (d : ℕ) (hd : 0<d) :
    ∃ a : Fin d → ZMod p, Irreducible (monicCandidate a) := by sorry
