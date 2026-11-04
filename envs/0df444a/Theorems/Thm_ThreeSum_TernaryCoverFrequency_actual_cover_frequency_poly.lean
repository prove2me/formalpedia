-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverFrequency_actual_cover_frequency_poly
-- name    : ThreeSum.TernaryCoverFrequency.actual_cover_frequency_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:23.153935+00:00
-- url     : https://prove2.me/theorems/06eb8824-5320-4a96-b824-fe37f82e7f7e
-- title:
--   Ternary Cover Frequency: actual cover frequency poly
-- statement:
--   The Ternary Cover Frequency construction uses the actual cover frequency poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L116-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L116-L128

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

theorem ThreeSum.TernaryCoverFrequency.actual_cover_frequency_poly (hp : 4 < p)
    (hlo : (vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)) ≤ p^2)
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)))
    (B k τ : ℕ) (hτ : 0 < τ)
    (hB : 8*(p+(fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ B*p)
    (hguard : 16*p^4*B^2*3^(4*k^2) ≤ τ^k*Fintype.card (ActualEdge m))
    (t : ZMod p × ZMod p) :
    Fintype.card (Weight m p) ≤ frequencyFactor m*
      (univ.filter fun w => Covers m p B τ w t).card := by sorry
