-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeTupleWitness_positional_ofFn
-- name    : ThreeSum.WeightedGlobalNativeTupleWitness.positional_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:48:26.647193+00:00
-- url     : https://prove2.me/theorems/17ddad71-9bea-4e85-9367-284b1d1f801d
-- title:
--   Weighted Global Native Tuple Witness: positional of Fn
-- statement:
--   The Weighted Global Native Tuple Witness construction uses the positional of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTupleWitness.lean#L31-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTupleWitness.lean#L31-L47

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

theorem ThreeSum.WeightedGlobalNativeTupleWitness.positional_ofFn {A : Type*} {r : ℕ} (xs : Fin r → A) (raw : A → ℤ)
    (v : Fin r → ZMod p) (hraw : ∀ i, raw (xs i)=(v i).val) :
    Radix.positionalHash (p : ℤ) raw (List.ofFn xs)=(coefficientCode v : ℤ) := by sorry
