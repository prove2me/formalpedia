-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_pair_encoding_injective
-- name    : ThreeSum.WeightedGlobalArenaPairModel.pair_encoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:28:52.299078+00:00
-- url     : https://prove2.me/theorems/e82ea11d-8873-493f-be27-b4848bc7e1d5
-- title:
--   Weighted Global Arena Pair Model: pair encoding injective
-- statement:
--   The Weighted Global Arena Pair Model construction uses the pair encoding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairModel.lean#L124-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairModel.lean#L124-L147

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

theorem ThreeSum.WeightedGlobalArenaPairModel.pair_encoding_injective {i : ℕ}
    (hi : i<(Host (r := r) maps τ cap localQ I).front.count) :
    Function.Injective (fun x : Pair (Host (r := r) maps τ cap localQ I) i =>
      ((x.val.1.1,x.val.2.1),edge hi x)) := by sorry
