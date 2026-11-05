-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankSweep_time_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankSweep.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:14:35.63518+00:00
-- url     : https://prove2.me/theorems/0fa91a51-d4b7-4e29-93fd-627f1a59eb59
-- title:
--   time_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankResources.lean#L22-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankResources.lean#L22-L26

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankResources
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankSweep

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankSweep.time_bound (N L n : ℕ) : time N L n≤4000*(N+1)*(N+L+1)*(n+1) := by sorry
