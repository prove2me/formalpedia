-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_allocateTime_le_bank_work
-- name    : ThreeSum.LightWeightedGlobalPrefixSetup.allocateTime_le_bank_work
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:54:01.37202+00:00
-- url     : https://prove2.me/theorems/800619e1-d60a-4e64-af20-94db380c97e0
-- title:
--   Light Weighted Global Prefix Setup: allocate Time le bank work
-- statement:
--   The Light Weighted Global Prefix Setup construction uses the allocate Time le bank work property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L285-L290
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L285-L290

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedGlobalPrefixSetup.allocateTime_le_bank_work {m : ℕ} (hm : 0<m) (j : ℕ) :
    allocateTime m j≤2000*(N m j+1)*(nb m j+1) := by sorry
