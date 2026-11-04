-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverFrequency_polynomial_frequency_scale
-- name    : ThreeSum.TernaryCoverFrequency.polynomial_frequency_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:59:30.080428+00:00
-- url     : https://prove2.me/theorems/440b1189-e92e-4dd4-81dd-7ea49dbe0249
-- title:
--   Ternary Cover Frequency: polynomial frequency scale
-- statement:
--   The Ternary Cover Frequency construction uses the polynomial frequency scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L104-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L104-L114

import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverFrequency
open Finset TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]

theorem ThreeSum.TernaryCoverFrequency.polynomial_frequency_scale
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2))) :
    4*p^4*3^16 ≤ frequencyFactor m*Fintype.card (ActualEdge m)^2 := by sorry
