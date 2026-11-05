-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_space_eq
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.space_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:14:27.195775+00:00
-- url     : https://prove2.me/theorems/3083815c-ca8b-41ef-8a0a-d83b3ff132d3
-- title:
--   space_eq
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankResources.lean#L47-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankResources.lean#L47-L49

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankResources
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.space_eq (a n N : ℕ) : space a n N=a+(3*N+8)*n+2*N+1 := by sorry
