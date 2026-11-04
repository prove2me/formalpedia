-- Prove2me | Theorems.Thm_ThreeSum_TernaryFixedDictionaries_left_native_fiber_cap
-- name    : ThreeSum.TernaryFixedDictionaries.left_native_fiber_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:24.980201+00:00
-- url     : https://prove2.me/theorems/504457a9-8a3e-43d9-a176-58d06d359b57
-- title:
--   Ternary Fixed Dictionaries: left native fiber cap
-- statement:
--   The Ternary Fixed Dictionaries construction uses the left native fiber cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L113-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L113-L153

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryFixedDictionaries.left_native_fiber_cap (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (a : ZMod p) :
    (leftNativeFiber (α := α) maps B a).card ≤ Fintype.card I*B := by sorry
