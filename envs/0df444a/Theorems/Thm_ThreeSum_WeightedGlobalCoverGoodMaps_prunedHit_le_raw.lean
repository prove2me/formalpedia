-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverGoodMaps_prunedHit_le_raw
-- name    : ThreeSum.WeightedGlobalCoverGoodMaps.prunedHit_le_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:25.699005+00:00
-- url     : https://prove2.me/theorems/32106775-fbc6-4a77-a9d4-6c2109d874c9
-- title:
--   Weighted Global Cover Good Maps: pruned Hit le raw
-- statement:
--   The Weighted Global Cover Good Maps construction uses the pruned Hit le raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverGoodMaps.lean#L88-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverGoodMaps.lean#L88-L99

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverGoodMaps
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open WeightedGlobalLocalParameters WeightedGlobalCoverActualMoment TernaryCoverMoments
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]

theorem ThreeSum.WeightedGlobalCoverGoodMaps.prunedHit_le_raw (B τ : ℕ) (w : Weight m p) (a b : ZMod p) :
    prunedHit m p B τ w a b ≤ TernaryCoverFibers.rawPairCount
      (leftHash (α := fixedAlpha m) (π := fixedPi m) w) (rightHash w) a b := by sorry
