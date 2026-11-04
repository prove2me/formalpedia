-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_dictionary_native
-- name    : ThreeSum.WeightedGlobalCanonicalSourceBank.dictionary_native
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:05:59.884682+00:00
-- url     : https://prove2.me/theorems/f4eb2931-a995-40e5-b121-96a9b24f6c5f
-- title:
--   Weighted Global Canonical Source Bank: dictionary native
-- statement:
--   The Weighted Global Canonical Source Bank construction uses the dictionary native property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L107-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L107-L115

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

theorem ThreeSum.WeightedGlobalCanonicalSourceBank.dictionary_native (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map (native right maps)) p r j.val=
      (TernaryExtensionEncoding.coefficientCode (nativeRow right maps B j) : ℤ) := by sorry
