-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_dimensions
-- name    : ThreeSum.LightWeightedGlobalPrefixSetup.dimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:51:35.342531+00:00
-- url     : https://prove2.me/theorems/2e62f35a-ab12-468c-8458-0ad2fde7892f
-- title:
--   Light Weighted Global Prefix Setup: dimensions
-- statement:
--   The Light Weighted Global Prefix Setup construction uses the dimensions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L49-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L49-L56

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

theorem ThreeSum.LightWeightedGlobalPrefixSetup.dimensions (m j : ℕ) :
    N m j=fixedLength (j*m) ∧ T m j=bankCut m j ∧ T m j≤ 1025*N m j := by sorry
