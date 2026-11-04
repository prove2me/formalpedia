-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_of_monic
-- name    : ThreeSum.TernaryExtensionEncoding.monicCandidate_of_monic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:28.591476+00:00
-- url     : https://prove2.me/theorems/87cfb433-b59e-45c9-a526-b81f11ff058a
-- title:
--   Ternary Extension Encoding: monic Candidate of monic
-- statement:
--   The Ternary Extension Encoding construction uses the monic Candidate of monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L47-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L47-L61

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.monicCandidate_of_monic {d : ℕ} {f : (ZMod p)[X]}
    (hf : f.Monic) (hd : f.natDegree=d) :
    monicCandidate (fun i : Fin d => f.coeff i.val)=f := by sorry
