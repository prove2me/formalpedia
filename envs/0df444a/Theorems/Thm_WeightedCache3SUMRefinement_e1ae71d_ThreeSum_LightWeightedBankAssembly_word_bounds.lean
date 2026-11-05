-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_word_bounds
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.word_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:14:17.23573+00:00
-- url     : https://prove2.me/theorems/ab17f462-da57-4119-810f-238f79d3086e
-- title:
--   word_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankResources.lean#L64-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/BankResources.lean#L64-L72

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankResources
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankAssembly.word_bounds (a n N V : ℕ) :
    space a n N≤word a n N V ∧ n+2^(2*N+1)+16≤word a n N V ∧
    2*N+3≤word a n N V ∧ 4*(4^N*V)+3≤word a n N V ∧
    valueBound N V≤word a n N V ∧ 4*(4^N*valueBound N V)+3≤word a n N V := by sorry
