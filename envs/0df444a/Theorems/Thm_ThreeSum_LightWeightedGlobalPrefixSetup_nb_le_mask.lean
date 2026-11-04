-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_nb_le_mask
-- name    : ThreeSum.LightWeightedGlobalPrefixSetup.nb_le_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:50:12.477312+00:00
-- url     : https://prove2.me/theorems/b31647cb-be92-4e17-860b-b71bb7cafccf
-- title:
--   Light Weighted Global Prefix Setup: nb le mask
-- statement:
--   The Light Weighted Global Prefix Setup construction uses the nb le mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L180-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L180-L185

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

theorem ThreeSum.LightWeightedGlobalPrefixSetup.nb_le_mask (m j : ℕ) : nb m j≤ 4^(N m j) := by sorry
