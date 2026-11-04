-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverScale_radix_power_upper
-- name    : ThreeSum.TernaryCoverScale.radix_power_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:55:22.845554+00:00
-- url     : https://prove2.me/theorems/b36a8026-fcae-4227-9b7e-f4e8da44d8f5
-- title:
--   Ternary Cover Scale: radix power upper
-- statement:
--   The Ternary Cover Scale construction uses the radix power upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L276-L298
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L276-L298

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency

theorem ThreeSum.TernaryCoverScale.radix_power_upper {m n : ℕ} (hm : 0 < m) (hn : 1 < n) :
    prime m^(radixLength m n) ≤ outputSize m^2*n^3 := by sorry
