-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverScale_capExponent_mul_upper
-- name    : ThreeSum.TernaryCoverScale.capExponent_mul_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:29.375199+00:00
-- url     : https://prove2.me/theorems/daa8857d-6d75-4343-801b-02ea16009a81
-- title:
--   Ternary Cover Scale: cap Exponent mul upper
-- statement:
--   The Ternary Cover Scale construction uses the cap Exponent mul upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L109-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L109-L116

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

theorem ThreeSum.TernaryCoverScale.capExponent_mul_upper (m k : ℕ) :
    k*capExponent (prime m) (sourceCap m (prime m)) k ≤ 12*fixedLength m+8*k^2+26+k := by sorry
