-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_menu_field_lower
-- name    : ThreeSum.TernaryExtensionEncoding.menu_field_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:21.530393+00:00
-- url     : https://prove2.me/theorems/af704847-ad17-4b6d-935e-cdee9b275863
-- title:
--   Ternary Extension Encoding: menu field lower
-- statement:
--   The Ternary Extension Encoding construction uses the menu field lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L89-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionCandidates.lean#L89-L91

import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
set_option maxHeartbeats 3000000
variable {p : ℕ} [Fact p.Prime]

theorem ThreeSum.TernaryExtensionEncoding.menu_field_lower (Λ K : ℕ) :
    8*(Λ+1)*p^(4*K)≤p^(menuDegree p Λ K) := by sorry
