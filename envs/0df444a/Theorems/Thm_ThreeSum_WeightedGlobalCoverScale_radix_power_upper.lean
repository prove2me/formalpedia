-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_radix_power_upper
-- name    : ThreeSum.WeightedGlobalCoverScale.radix_power_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:26.425758+00:00
-- url     : https://prove2.me/theorems/75f1e1d4-50c6-4a1d-8c63-71ec24bf4dcc
-- title:
--   Weighted Global Cover Scale: radix power upper
-- statement:
--   The Weighted Global Cover Scale construction uses the radix power upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L283-L305
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L283-L305

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency

theorem ThreeSum.WeightedGlobalCoverScale.radix_power_upper {m n : ℕ} (hm : 0 < m) (hn : 1 < n) :
    prime m^(radixLength m n) ≤ outputSize m^2*n^3 := by sorry
