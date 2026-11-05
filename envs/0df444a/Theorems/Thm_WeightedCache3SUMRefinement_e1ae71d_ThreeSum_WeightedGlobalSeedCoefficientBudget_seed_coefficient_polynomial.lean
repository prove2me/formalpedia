-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSeedCoefficientBudget_seed_coefficient_polynomial
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSeedCoefficientBudget.seed_coefficient_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:47:17.949427+00:00
-- url     : https://prove2.me/theorems/93b0a55d-0b13-4304-9dab-cc1730e961e4
-- title:
--   seed_coefficient_polynomial
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L45-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySeedCoefficientBudget.lean#L45-L65

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSeedCoefficientBudget.seed_coefficient_polynomial (K p B A : ℕ) :
    ∃ C d : ℕ, ∀J j, j≤J→
      seedCoefficient K J p B (A*(p+1)^j) j≤C*(J+1)^d := by sorry
