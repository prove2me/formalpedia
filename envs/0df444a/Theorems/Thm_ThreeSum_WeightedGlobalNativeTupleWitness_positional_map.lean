-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeTupleWitness_positional_map
-- name    : ThreeSum.WeightedGlobalNativeTupleWitness.positional_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:48:32.977891+00:00
-- url     : https://prove2.me/theorems/0ece24a6-d9f3-406c-9704-0e5876f95bf4
-- title:
--   Weighted Global Native Tuple Witness: positional map
-- statement:
--   The Weighted Global Native Tuple Witness construction uses the positional map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTupleWitness.lean#L19-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTupleWitness.lean#L19-L23

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

theorem ThreeSum.WeightedGlobalNativeTupleWitness.positional_map {A B : Type*} (p : ℤ) (f : A → B) (g : B → ℤ) (xs : List A) :
    Radix.positionalHash p (g ∘ f) xs=Radix.positionalHash p g (xs.map f) := by sorry
