-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverFrequency_covers_raw_cap
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverFrequency.covers_raw_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:21:41.366462+00:00
-- url     : https://prove2.me/theorems/03b73964-6dc6-4150-a9ce-c299fc4a6d61
-- title:
--   covers_raw_cap
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverFrequency.lean#L139-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverFrequency.lean#L139-L147

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverFrequency
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverFrequency
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverFrequency.covers_raw_cap {B τ : ℕ} {w : Weight m p} {t : ZMod p × ZMod p}
    (hc : Covers m p B τ w t) : rawCap (fixedAlpha m) (fixedPi m) w ≤ τ := by sorry
