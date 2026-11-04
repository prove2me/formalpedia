-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverFrequency_polynomial_frequency_scale
-- name    : ThreeSum.WeightedGlobalCoverFrequency.polynomial_frequency_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:24.625335+00:00
-- url     : https://prove2.me/theorems/818fad86-672a-424b-9cce-b23dd254fbf4
-- title:
--   Weighted Global Cover Frequency: polynomial frequency scale
-- statement:
--   The Weighted Global Cover Frequency construction uses the polynomial frequency scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverFrequency.lean#L111-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverFrequency.lean#L111-L121

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverFrequency
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]

theorem ThreeSum.WeightedGlobalCoverFrequency.polynomial_frequency_scale
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2))) :
    4*p^4*3^16 ≤ frequencyFactor m*Fintype.card (ActualEdge m)^2 := by sorry
