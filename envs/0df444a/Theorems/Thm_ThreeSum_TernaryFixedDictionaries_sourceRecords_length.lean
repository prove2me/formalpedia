-- Prove2me | Theorems.Thm_ThreeSum_TernaryFixedDictionaries_sourceRecords_length
-- name    : ThreeSum.TernaryFixedDictionaries.sourceRecords_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:58:35.186326+00:00
-- url     : https://prove2.me/theorems/f37c2735-5316-4ccc-bfb2-747cbb48689f
-- title:
--   Ternary Fixed Dictionaries: source Records length
-- statement:
--   The Ternary Fixed Dictionaries construction uses the source Records length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L26-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L26-L29

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryFixedDictionaries.sourceRecords_length (L : ℕ) (α : DigitType) :
    (sourceRecords L α I).length = Fintype.card I*(vertices L α).card := by sorry
