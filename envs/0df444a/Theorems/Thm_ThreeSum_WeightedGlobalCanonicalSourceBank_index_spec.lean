-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_index_spec
-- name    : ThreeSum.WeightedGlobalCanonicalSourceBank.index_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:03:59.894196+00:00
-- url     : https://prove2.me/theorems/e6aba4b2-a270-4d96-a3eb-61cf20ca0b2e
-- title:
--   Weighted Global Canonical Source Bank: index spec
-- statement:
--   The Weighted Global Canonical Source Bank construction uses the index spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L72-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L72-L77

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Theorems.Thm_ThreeSum_TernaryBankStageModel_index_spec
import Theorems.Thm_ThreeSum_WeightedBankStageModel_index_spec

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCanonicalSourceBank
open TernaryJointType TernaryCanonicalDictionaries WeightedGlobalRepeatedWords
open WeightedGlobalTupleDictionaryDecode TernaryCodeSemantics WeightedAddresses
open TernaryCoverLocal TernaryFixedDictionaries WeightedGlobalLocalParameters
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalCanonicalSourceBank.index_spec {N T : ℕ} (w : TritWord N) (hw : WeightedGlobalBank.cacheCost w≤T) :
    (codes N T).idxOf (address w)<(codes N T).length ∧
      (codes N T).getD ((codes N T).idxOf (address w)) 0=address w := by sorry
