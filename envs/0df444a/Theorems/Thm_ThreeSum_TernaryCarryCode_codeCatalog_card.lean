-- Prove2me | Theorems.Thm_ThreeSum_TernaryCarryCode_codeCatalog_card
-- name    : ThreeSum.TernaryCarryCode.codeCatalog_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:27.056252+00:00
-- url     : https://prove2.me/theorems/adfec1a7-0f62-416e-aa4b-f078c555b53f
-- title:
--   Ternary Carry Code: code Catalog card
-- statement:
--   The Ternary Carry Code construction uses the code Catalog card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L90-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L90-L91

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernaryCarryCode.codeCatalog_card (J : ℕ) : (codeCatalog J).card≤2^J := by sorry
