-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeTupleWitness_positional_cast_digits
-- name    : ThreeSum.WeightedGlobalNativeTupleWitness.positional_cast_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:03.050773+00:00
-- url     : https://prove2.me/theorems/793c1c27-caed-4642-9e50-4a174fe4320a
-- title:
--   Weighted Global Native Tuple Witness: positional cast digits
-- statement:
--   The Weighted Global Native Tuple Witness construction uses the positional cast digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTupleWitness.lean#L25-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTupleWitness.lean#L25-L29

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryRepeatedWords
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTupleWitness
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeTupleWitness
open Finset TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalCoverGoodMaps
open WeightedGlobalNativeCoverWitness TernaryExtensionEncoding TernaryFixedDictionaries
open scoped BigOperators
variable {p m : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalNativeTupleWitness.positional_cast_digits (p : ℕ) (xs : List ℕ) :
    Radix.positionalHash (p : ℤ) (fun a : ℕ => (a : ℤ)) xs=((Nat.ofDigits p xs : ℕ) : ℤ) := by sorry
