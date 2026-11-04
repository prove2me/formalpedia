-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverGoodMaps_prunedHit_le_raw
-- name    : ThreeSum.TernaryCoverGoodMaps.prunedHit_le_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:09.704189+00:00
-- url     : https://prove2.me/theorems/bf7f26c2-edd1-429c-bf07-cc5e3ae1e86a
-- title:
--   Ternary Cover Good Maps: pruned Hit le raw
-- statement:
--   The Ternary Cover Good Maps construction uses the pruned Hit le raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGoodMaps.lean#L81-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGoodMaps.lean#L81-L92

import Definitions.Def_Submission_ThreeSum_TernaryCoverActualMoment
import Definitions.Def_Submission_ThreeSum_Cover
import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverGoodMaps
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open TernaryLocalParameters TernaryCoverActualMoment TernaryCoverMoments
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]

theorem ThreeSum.TernaryCoverGoodMaps.prunedHit_le_raw (B τ : ℕ) (w : Weight m p) (a b : ZMod p) :
    prunedHit m p B τ w a b ≤ TernaryCoverFibers.rawPairCount
      (leftHash (α := fixedAlpha m) (π := fixedPi m) w) (rightHash w) a b := by sorry
