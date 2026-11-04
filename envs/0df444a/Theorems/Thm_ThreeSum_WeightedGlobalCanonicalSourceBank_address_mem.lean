-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_address_mem
-- name    : ThreeSum.WeightedGlobalCanonicalSourceBank.address_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:06:01.276198+00:00
-- url     : https://prove2.me/theorems/a602b61d-d00d-4f8d-8f5b-4f975a7befaf
-- title:
--   Weighted Global Canonical Source Bank: address mem
-- statement:
--   The Weighted Global Canonical Source Bank construction uses the address mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L64-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L64-L70

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCanonicalSourceBank
open TernaryJointType TernaryCanonicalDictionaries WeightedGlobalRepeatedWords
open WeightedGlobalTupleDictionaryDecode TernaryCodeSemantics WeightedAddresses
open TernaryCoverLocal TernaryFixedDictionaries WeightedGlobalLocalParameters
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalCanonicalSourceBank.address_mem {N T : ℕ} (w : TritWord N) (hw : WeightedGlobalBank.cacheCost w≤T) :
    address w∈codes N T := by sorry
