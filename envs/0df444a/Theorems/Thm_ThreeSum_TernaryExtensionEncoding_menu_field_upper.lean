-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_menu_field_upper
-- name    : ThreeSum.TernaryExtensionEncoding.menu_field_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:40.142489+00:00
-- url     : https://prove2.me/theorems/eef571a7-f183-4bd5-b01a-8dc4be746c49
-- title:
--   Ternary Extension Encoding: menu field upper
-- statement:
--   The Ternary Extension Encoding construction uses the menu field upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L93-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L93-L107

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.menu_field_upper (Λ K : ℕ) :
    p^(menuDegree p Λ K)≤8*p^(4*K+1)*(Λ+1) := by sorry
