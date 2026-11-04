-- Prove2me | Theorems.Thm_ThreeSum_TernaryFixedDictionaries_outputRecords_length
-- name    : ThreeSum.TernaryFixedDictionaries.outputRecords_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:58:32.396812+00:00
-- url     : https://prove2.me/theorems/48ca0f49-34e6-416a-9bc7-307dd4c3aba0
-- title:
--   Ternary Fixed Dictionaries: output Records length
-- statement:
--   The Ternary Fixed Dictionaries construction uses the output Records length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L31-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L31-L34

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryFixedDictionaries.outputRecords_length (L : ℕ) (π : DigitType) :
    (outputRecords L π I).length = Fintype.card I*(vertices L π).card := by sorry
