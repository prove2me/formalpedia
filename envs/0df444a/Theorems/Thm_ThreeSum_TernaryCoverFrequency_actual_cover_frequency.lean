-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverFrequency_actual_cover_frequency
-- name    : ThreeSum.TernaryCoverFrequency.actual_cover_frequency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:59:19.255448+00:00
-- url     : https://prove2.me/theorems/13836063-f6ef-45e7-988c-6b0b9c03facd
-- title:
--   Ternary Cover Frequency: actual cover frequency
-- statement:
--   The Ternary Cover Frequency construction uses the actual cover frequency property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L64-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L64-L83

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

theorem ThreeSum.TernaryCoverFrequency.actual_cover_frequency (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (B k τ a : ℕ) (hτ : 0 < τ)
    (hB : 8 * (p + (fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ B * p)
    (hguard : 16*p^4*B^2*3^(4*k^2) ≤ τ^k*Fintype.card (ActualEdge m))
    (hscale : 4*p^4*3^16 ≤ a*Fintype.card (ActualEdge m)^2) (t : ZMod p × ZMod p) :
    Fintype.card (Weight m p) ≤ a * (univ.filter fun w => Covers m p B τ w t).card := by sorry
