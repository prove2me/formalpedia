-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverFrequency_greedy_covers
-- name    : ThreeSum.TernaryCoverFrequency.greedy_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:43.31719+00:00
-- url     : https://prove2.me/theorems/d92d3d2b-e4ab-4e11-8278-14a881f8eafd
-- title:
--   Ternary Cover Frequency: greedy covers
-- statement:
--   The existing exhaustive first-maximum greedy routine covers every
--   ordered target with an actual retained edge and a valid global raw cap.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L87-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFrequency.lean#L87-L99

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

theorem ThreeSum.TernaryCoverFrequency.greedy_covers (maps : List (Weight m p)) (hall : ∀ w, w ∈ maps)
    (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (B k τ a : ℕ) (ha : 1 < a) (hτ : 0 < τ)
    (hB : 8 * (p + (fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ B * p)
    (hguard : 16*p^4*B^2*3^(4*k^2) ≤ τ^k*Fintype.card (ActualEdge m))
    (hscale : 4*p^4*3^16 ≤ a*Fintype.card (ActualEdge m)^2) (t : ZMod p × ZMod p) :
    ∃ w ∈ Cover.greedyChoices maps (Covers m p B τ) univ (a*(Nat.log2 (p^2)+1)),
      Covers m p B τ w t := by sorry
