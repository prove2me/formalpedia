-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_cost_add_deficit
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.cost_add_deficit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:10:16.918369+00:00
-- url     : https://prove2.me/theorems/5cd51bce-3337-4227-a12f-9b6e2f9c3b84
-- title:
--   cost_add_deficit
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalBank.lean#L24-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalBank.lean#L24-L26

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_cost_add_deficit

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
open TernaryJointType

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.cost_add_deficit {N : ℕ} {R Q : TritWord N} (h : Below R Q) :
    cacheCost R+deficit Q R=cacheCost Q := by sorry
