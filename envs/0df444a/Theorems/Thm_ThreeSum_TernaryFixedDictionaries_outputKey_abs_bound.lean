-- Prove2me | Theorems.Thm_ThreeSum_TernaryFixedDictionaries_outputKey_abs_bound
-- name    : ThreeSum.TernaryFixedDictionaries.outputKey_abs_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:20.931473+00:00
-- url     : https://prove2.me/theorems/3628d5c3-20de-4edf-b4f5-f9ed140708cf
-- title:
--   Ternary Fixed Dictionaries: output Key abs bound
-- statement:
--   The Ternary Fixed Dictionaries construction uses the output Key abs bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L48-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L48-L50

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryFixedDictionaries.outputKey_abs_bound (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : OutputBlock L π I) : |blockKey maps r| ≤ ((2*L+2)*p : ℕ) := by sorry
