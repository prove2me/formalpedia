-- Prove2me | Theorems.Thm_ThreeSum_TernaryFixedDictionaries_rightKey_abs_bound
-- name    : ThreeSum.TernaryFixedDictionaries.rightKey_abs_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:54.054819+00:00
-- url     : https://prove2.me/theorems/52cc930a-b09e-41d2-9985-6db1bc5d087e
-- title:
--   Ternary Fixed Dictionaries: right Key abs bound
-- statement:
--   The Ternary Fixed Dictionaries construction uses the right Key abs bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L42-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L42-L46

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryFixedDictionaries.rightKey_abs_bound (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : |rightKey maps r| ≤ ((2*L+1)*p : ℕ) := by sorry
