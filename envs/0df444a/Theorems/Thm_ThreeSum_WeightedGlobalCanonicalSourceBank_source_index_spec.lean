-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_source_index_spec
-- name    : ThreeSum.WeightedGlobalCanonicalSourceBank.source_index_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:05:24.807724+00:00
-- url     : https://prove2.me/theorems/a33a87b1-2690-4311-9486-f995a017d3db
-- title:
--   Weighted Global Canonical Source Bank: source index spec
-- statement:
--   The Weighted Global Canonical Source Bank construction uses the source index spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L79-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L79-L90

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

theorem ThreeSum.WeightedGlobalCanonicalSourceBank.source_index_spec (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r)) :
    let code := (LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map wordCode)
      (4^fixedLength m) r j.val).toNat
    (codes (r*fixedLength m) (LightWeightedGlobalPrefixSetup.T m r)).idxOf code<
      (codes (r*fixedLength m) (LightWeightedGlobalPrefixSetup.T m r)).length ∧
      (codes (r*fixedLength m) (LightWeightedGlobalPrefixSetup.T m r)).getD
        ((codes (r*fixedLength m) (LightWeightedGlobalPrefixSetup.T m r)).idxOf code) 0=code := by sorry
