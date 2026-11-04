-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_block_injective
-- name    : ThreeSum.WeightedGlobalCanonicalSourceBank.block_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:05:43.144774+00:00
-- url     : https://prove2.me/theorems/e2c4e46e-b75a-4b8e-9dfc-3766f9148d92
-- title:
--   Weighted Global Canonical Source Bank: block injective
-- statement:
--   The Weighted Global Canonical Source Bank construction uses the block injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L157-L162
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L157-L162

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeBlockPairs
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryDecode
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalSourceBank
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCanonicalSourceBank
open TernaryJointType TernaryCanonicalDictionaries WeightedGlobalRepeatedWords
open WeightedGlobalTupleDictionaryDecode TernaryCodeSemantics WeightedAddresses
open TernaryCoverLocal TernaryFixedDictionaries WeightedGlobalLocalParameters
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalCanonicalSourceBank.block_injective (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p) (B : ℕ) :
    Function.Injective (block (r := r) right maps B) := by sorry
