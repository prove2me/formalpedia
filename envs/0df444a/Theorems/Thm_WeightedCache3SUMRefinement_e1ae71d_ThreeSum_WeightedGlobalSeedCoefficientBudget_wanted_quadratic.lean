-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSeedCoefficientBudget_wanted_quadratic
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSeedCoefficientBudget.wanted_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:49:17.137197+00:00
-- url     : https://prove2.me/theorems/e852e27c-8914-4180-8c08-59b32569f24b
-- title:
--   wanted_quadratic
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L27-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L27-L41

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSeedCoefficientBudget.wanted_quadratic (p A J j : ℕ) (hj : j≤J) :
    (LightTernaryWantedCanonical.overhead p (A*(p+1)^j)+
      LightTernaryWantedCanonical.stepCost (A*(p+1)^j)+40)*(j+1)≤
      (1000*(A+2*p+4))*(J+1)^2 := by sorry
