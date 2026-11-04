-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCanonicalSourceBank_source_rows
-- name    : ThreeSum.WeightedGlobalCanonicalSourceBank.source_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:06:20.336964+00:00
-- url     : https://prove2.me/theorems/a82cb463-e7fc-463f-aa47-feb25c2f3626
-- title:
--   Weighted Global Canonical Source Bank: source rows
-- statement:
--   The actual residue join forces every selected ORIGINAL hash row.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L129-L142
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalSourceBank.lean#L129-L142

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

theorem ThreeSum.WeightedGlobalCanonicalSourceBank.source_rows (right : Bool)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin (fixedLength m))→ZMod p)
    (B : ℕ) (j : Fin ((records (α := fixedAlpha m) right maps B).length^r))
    (original : Fin r→ZMod p)
    (hjoin : ((p^r : ℕ) : ℤ)∣(TernaryExtensionEncoding.coefficientCode original : ℤ)-
      LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) right maps B).map (native right maps)) p r j.val) :
    original=nativeRow right maps B j := by sorry
