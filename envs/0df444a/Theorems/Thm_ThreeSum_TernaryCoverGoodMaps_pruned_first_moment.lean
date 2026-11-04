-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverGoodMaps_pruned_first_moment
-- name    : ThreeSum.TernaryCoverGoodMaps.pruned_first_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:57.944241+00:00
-- url     : https://prove2.me/theorems/f1b500ee-de14-46e5-8eab-81d397643ddc
-- title:
--   Ternary Cover Good Maps: pruned first moment
-- statement:
--   The Ternary Cover Good Maps construction uses the pruned first moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGoodMaps.lean#L41-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverGoodMaps.lean#L41-L79

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

theorem ThreeSum.TernaryCoverGoodMaps.pruned_first_moment (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (B k τ : ℕ) (hτ : 0 < τ)
    (hB : 8 * (p + (fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ B * p)
    (hguard : 16*p^4*B^2*3^(4*k^2) ≤ τ^k*Fintype.card (ActualEdge m))
    (a b : ZMod p) :
    Fintype.card (ActualEdge m) * Fintype.card (Weight m p) ≤
      2 * p ^ 2 * ∑ w, prunedHit m p B τ w a b := by sorry
