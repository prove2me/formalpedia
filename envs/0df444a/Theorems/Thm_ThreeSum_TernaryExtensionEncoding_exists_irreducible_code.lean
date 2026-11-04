-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_exists_irreducible_code
-- name    : ThreeSum.TernaryExtensionEncoding.exists_irreducible_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:57.505172+00:00
-- url     : https://prove2.me/theorems/ccfeecce-169b-4d0c-9563-1fba83e569c7
-- title:
--   Ternary Extension Encoding: exists irreducible code
-- statement:
--   The Ternary Extension Encoding construction uses the exists irreducible code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoefficientCodes.lean#L68-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoefficientCodes.lean#L68-L72

import Definitions.Def_Submission_ThreeSum_TernaryExtensionDecoded
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryExtensionEncoding.exists_irreducible_code (d : ℕ) (hd : 0<d) :
    ∃ code<p^d, Irreducible (monicOfCode (p := p) d code) := by sorry
