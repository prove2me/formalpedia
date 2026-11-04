-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedReduction_carryCatalog_card
-- name    : ThreeSum.TernarySignedReduction.carryCatalog_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:38:01.112783+00:00
-- url     : https://prove2.me/theorems/23be3cd2-5d13-4175-bea7-561304816e4b
-- title:
--   Ternary Signed Reduction: carry Catalog card
-- statement:
--   The Ternary Signed Reduction construction uses the carry Catalog card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L62-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L62-L72

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset

theorem ThreeSum.TernarySignedReduction.carryCatalog_card (J : ℕ) : (carryCatalog J).card ≤ 2^J := by sorry
