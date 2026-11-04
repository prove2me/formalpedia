-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverScale_prime_square_le_cube
-- name    : ThreeSum.TernaryCoverScale.prime_square_le_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:51.382873+00:00
-- url     : https://prove2.me/theorems/d2166a05-2d9d-476e-95ec-48073ae389ea
-- title:
--   Ternary Cover Scale: prime square le cube
-- statement:
--   The Ternary Cover Scale construction uses the prime square le cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L264-L272
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L264-L272

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

theorem ThreeSum.TernaryCoverScale.prime_square_le_cube {m : ℕ} (hm : 0 < m) : prime m^2 ≤ outputSize m^3 := by sorry
