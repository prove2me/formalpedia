-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalBank_mem_nearWords
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.mem_nearWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:17:41.854244+00:00
-- url     : https://prove2.me/theorems/6de47959-144d-45a1-bbd4-c90e2f07601e
-- title:
--   mem_nearWords
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalBank.lean#L19-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalBank.lean#L19-L20

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedNearBankEnumeration.mem_nearWords


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
open TernaryJointType

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.mem_nearWords {N D : ℕ} {R Q : TritWord N} :
    R∈nearWords Q D ↔ Below R Q ∧ deficit Q R≤D := by sorry
