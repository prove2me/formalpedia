-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeCoverWitness_retained_edge
-- name    : ThreeSum.WeightedGlobalNativeCoverWitness.retained_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:44.900472+00:00
-- url     : https://prove2.me/theorems/385b8ea1-16ae-43a8-8554-a202bff44cba
-- title:
--   Weighted Global Native Cover Witness: retained edge
-- statement:
--   The Weighted Global Native Cover Witness construction uses the retained edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L21-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeCoverWitness.lean#L21-L40

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeCoverWitness
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency TernaryFixedDictionaries
open TernaryCanonicalDictionaries
variable {m p : ℕ} [Fact p.Prime]
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalNativeCoverWitness.retained_edge {B τ : ℕ}
    (w : Weight m p) (a b : ZMod p) (hc : Covers m p B τ w (a,b)) :
    w∉rawBadMaps m p τ ∧ ∃ e : ActualEdge m,
      leftHash w e=a ∧ rightHash w e=b ∧
      TernaryCoverTrimming.bucketSize (fieldVertices (fixedLength m) p (fixedAlpha m))
        TernaryCoverHashes.leftVector w a≤B ∧
      TernaryCoverTrimming.bucketSize (fieldVertices (fixedLength m) p (fixedAlpha m))
        TernaryCoverHashes.rightVector w b≤B := by sorry
