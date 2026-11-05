-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverCapParameters_explicit_greedy_covers
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverCapParameters.explicit_greedy_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:22:59.455391+00:00
-- url     : https://prove2.me/theorems/cdf45c7a-2c33-47d1-8da8-216f0866e0d5
-- title:
--   explicit_greedy_covers
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L99-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L99-L113

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverCapParameters.explicit_greedy_covers (m p : ℕ) [Fact p.Prime]
    (maps : List (Weight m p)) (hall : ∀ w, w ∈ maps) (hp : 4 < p)
    (hlo : (vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)) ≤ p^2)
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)))
    (k : ℕ) (hk : 0 < k) (t : ZMod p × ZMod p) :
    ∃ w ∈ Cover.greedyChoices maps
        (Covers m p (sourceCap m p) (rawThreshold p (sourceCap m p) k)) Finset.univ
        (frequencyFactor m*(Nat.log2 (p^2)+1)),
      Covers m p (sourceCap m p) (rawThreshold p (sourceCap m p) k) w t := by sorry
