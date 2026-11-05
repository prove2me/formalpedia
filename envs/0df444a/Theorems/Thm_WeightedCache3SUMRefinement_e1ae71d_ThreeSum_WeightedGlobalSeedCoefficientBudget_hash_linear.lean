-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSeedCoefficientBudget_hash_linear
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSeedCoefficientBudget.hash_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:45:39.504381+00:00
-- url     : https://prove2.me/theorems/32e90d1a-1701-4953-90cb-977038e83306
-- title:
--   hash_linear
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L18-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L18-L23

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryActualPrefixRuntime
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySeedCoefficientBudget
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSeedCoefficientBudget
open WeightedGlobalActualPrefixRuntime
set_option maxHeartbeats 6000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSeedCoefficientBudget.hash_linear (J p B : ℕ) :
    LightSignedRowHash.time (J+2) p B+120≤
      (596+80*p*(p+B))*(J+1) := by sorry
