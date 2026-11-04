-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_injective
-- name    : ThreeSum.TernaryExtensionEncoding.monicCandidate_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:32.918601+00:00
-- url     : https://prove2.me/theorems/a27f6dd4-04ab-49c9-bf77-a0da1681b0df
-- title:
--   Ternary Extension Encoding: monic Candidate injective
-- statement:
--   The Ternary Extension Encoding construction uses the monic Candidate injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L63-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L63-L68

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.monicCandidate_injective (d : ℕ) :
    Function.Injective (monicCandidate (p := p) (d := d)) := by sorry
