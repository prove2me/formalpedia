-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_degree
-- name    : ThreeSum.TernaryExtensionEncoding.monicCandidate_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:02:55.205427+00:00
-- url     : https://prove2.me/theorems/78e7b878-f6ab-47ac-8d04-44fb13448b4c
-- title:
--   Ternary Extension Encoding: monic Candidate degree
-- statement:
--   The Ternary Extension Encoding construction uses the monic Candidate degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L35-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L35-L40

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.monicCandidate_degree {d : ℕ} (a : Fin d → ZMod p) :
    (monicCandidate a).natDegree=d := by sorry
