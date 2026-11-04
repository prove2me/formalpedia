-- Prove2me | Theorems.Thm_ThreeSum_TernaryCarryCode_carryCatalog_eq_codes
-- name    : ThreeSum.TernaryCarryCode.carryCatalog_eq_codes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:09.532268+00:00
-- url     : https://prove2.me/theorems/9094427e-8cc8-4769-8133-108641e5bd04
-- title:
--   Ternary Carry Code: carry Catalog eq codes
-- statement:
--   The Ternary Carry Code construction uses the carry Catalog eq codes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L93-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L93-L104

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernaryCarryCode.carryCatalog_eq_codes (J : ℕ) :
    carryCatalog J=(codeCatalog J).image (carryFromCode J) := by sorry
