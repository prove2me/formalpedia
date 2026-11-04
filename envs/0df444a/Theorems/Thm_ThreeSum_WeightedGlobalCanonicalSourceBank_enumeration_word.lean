-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_enumeration_word
-- name    : ThreeSum.WeightedGlobalCanonicalSourceBank.enumeration_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:06:07.964792+00:00
-- url     : https://prove2.me/theorems/6857782d-1e48-4c70-83a9-ae60cc9ee35b
-- title:
--   Weighted Global Canonical Source Bank: enumeration word
-- statement:
--   The Weighted Global Canonical Source Bank construction uses the enumeration word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L93-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L93-L98

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

theorem ThreeSum.WeightedGlobalCanonicalSourceBank.enumeration_word {N T : ℕ} (Eword : ℕ→TritWord N)
    (hE : ∀ k<(codes N T).length, address (Eword k)=(codes N T).getD k 0)
    (w : TritWord N) (hw : WeightedGlobalBank.cacheCost w≤T) :
    Eword ((codes N T).idxOf (address w))=w := by sorry
