-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_outputSize_ge_sixteen
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale.outputSize_ge_sixteen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:24:25.338925+00:00
-- url     : https://prove2.me/theorems/90eda580-4990-4c86-a005-3b64d3c02ece
-- title:
--   outputSize_ge_sixteen
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverScale.lean#L263-L269
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryCoverScale.lean#L263-L269

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale.outputSize_ge_sixteen {m : ℕ} (hm : 0 < m) : 16 ≤ outputSize m := by sorry
