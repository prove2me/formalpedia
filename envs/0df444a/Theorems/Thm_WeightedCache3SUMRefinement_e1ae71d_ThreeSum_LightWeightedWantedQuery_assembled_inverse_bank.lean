-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedQuery_assembled_inverse_bank
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery.assembled_inverse_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:47:55.246382+00:00
-- url     : https://prove2.me/theorems/78b739f7-de31-4ff8-99c3-f1777f92f9e8
-- title:
--   assembled_inverse_bank
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/WantedQuery.lean#L140-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/WantedQuery.lean#L140-L145

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearPair
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenPhysical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankAssembly
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_WantedQuery
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery.assembled_inverse_bank {N T n base : ℕ} (E : Enumeration N T n)
    (F G : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hs : LightWeightedBankSweep.Stages E
      (fun k => stageValue k (LightWeightedBankAssembly.product F G)) base N μ) :
    LightWeightedBankSweep.Stages E (fun k => stageValue k (H F G)) base N μ := by sorry
