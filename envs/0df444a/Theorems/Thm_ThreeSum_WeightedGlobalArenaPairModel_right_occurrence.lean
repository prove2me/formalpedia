-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_right_occurrence
-- name    : ThreeSum.WeightedGlobalArenaPairModel.right_occurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:27:46.909441+00:00
-- url     : https://prove2.me/theorems/1d23de23-6ee9-44e0-9d41-6a725b0d7347
-- title:
--   Weighted Global Arena Pair Model: right occurrence
-- statement:
--   The Weighted Global Arena Pair Model construction uses the right occurrence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairModel.lean#L63-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairModel.lean#L63-L74

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairModel
import Theorems.Thm_Light_Ends_block

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

theorem ThreeSum.WeightedGlobalArenaPairModel.right_occurrence {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i) :
    (fun t => (WeightedGlobalCanonicalSourceBank.block true maps cap (rightIndex x) t).1)=
      (fun t => (outputBlock (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) (I := I) hi t).1) := by sorry
