-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_nb_eq_bankSize
-- name    : ThreeSum.LightWeightedGlobalPrefixSetup.nb_eq_bankSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:51:42.577473+00:00
-- url     : https://prove2.me/theorems/7498a72a-a82a-4576-aac0-e3b4d0eeff79
-- title:
--   Light Weighted Global Prefix Setup: nb eq bank Size
-- statement:
--   The Light Weighted Global Prefix Setup construction uses the nb eq bank Size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L58-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L58-L61

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

theorem ThreeSum.LightWeightedGlobalPrefixSetup.nb_eq_bankSize (m j : ℕ) : nb m j=bankSize m j := by sorry
