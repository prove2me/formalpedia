-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_left_hash
-- name    : ThreeSum.WeightedGlobalArenaPairModel.left_hash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:33:08.948642+00:00
-- url     : https://prove2.me/theorems/4e4500f9-2687-48c5-ae25-08b8f2fed46a
-- title:
--   Weighted Global Arena Pair Model: left hash
-- statement:
--   The Weighted Global Arena Pair Model construction uses the left hash property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairModel.lean#L100-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPairModel.lean#L100-L110

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

theorem ThreeSum.WeightedGlobalArenaPairModel.left_hash {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i) (t : Fin r) :
    WeightedGlobalCanonicalSourceBank.nativeRow false maps cap (leftIndex x) t=
      leftHash (maps (outputBlock (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) (I := I) hi t).1)
        (edge hi x t) := by sorry
