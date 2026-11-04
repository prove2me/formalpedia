-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_original_hash_sum
-- name    : ThreeSum.WeightedGlobalArenaPairModel.original_hash_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:28:56.350234+00:00
-- url     : https://prove2.me/theorems/fbf487e0-d996-478a-b11b-5dc7c60562e3
-- title:
--   Weighted Global Arena Pair Model: original hash sum
-- statement:
--   The Weighted Global Arena Pair Model construction uses the original hash sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairModel.lean#L150-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairModel.lean#L150-L172

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairModel
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPairModel
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalNativePairMoments WeightedGlobalArenaSourceModel TernaryCoverLocal
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (localQ : WeightedGlobalGoodOutputCatalog.Output m) (I : Input)
variable {maps τ cap localQ I}

theorem ThreeSum.WeightedGlobalArenaPairModel.original_hash_sum {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i)
    (B C O : ℕ→Fin r→ZMod p)
    (hB : ∀ j<I.nB, I.leftInput j=(TernaryExtensionEncoding.coefficientCode (B j) : ℤ))
    (hC : ∀ j<I.nC, I.rightInput j=(TernaryExtensionEncoding.coefficientCode (C j) : ℤ))
    (hO : ∀ j<I.requesterCount, I.targets j=(TernaryExtensionEncoding.coefficientCode (O j) : ℤ)) :
    B x.val.1.1+C x.val.2.1=
      O (WeightedGlobalArenaQueryModel.descriptor maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩).1 := by sorry
