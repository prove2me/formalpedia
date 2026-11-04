-- Prove2me | Theorems.Thm_ThreeSum_LightQueryWeights_weights_of_segment
-- name    : ThreeSum.LightQueryWeights.weights_of_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:17:03.869291+00:00
-- url     : https://prove2.me/theorems/e171a4ca-120a-4ad1-88be-61ce56d60f66
-- title:
--   Light Query Weights: weights of segment
-- statement:
--   The Light Query Weights construction uses the weights of segment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryWeights.lean#L161-L167
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryWeights.lean#L161-L167

import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightQueryWeights
set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryWeights
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightQueryWeights.weights_of_segment {μ : ℕ → ℤ} {W dst : ℕ} {Q : Finset (Fin W)}
    (hseg : SegN μ dst (selectedPowers Q W)) :
    LightWeightedEnumeration.Weights μ dst Q.card (weights Q) := by sorry
