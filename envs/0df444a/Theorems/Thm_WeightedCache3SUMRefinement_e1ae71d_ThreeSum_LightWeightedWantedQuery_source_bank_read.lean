-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedWantedQuery_source_bank_read
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery.source_bank_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:48:54.083322+00:00
-- url     : https://prove2.me/theorems/9d75ee3d-1551-4958-ad1e-dad8c6857191
-- title:
--   source_bank_read
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/WantedQuery.lean#L126-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/WantedQuery.lean#L126-L131

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedWantedQuery.source_bank_read {N T n base : ℕ} (E : Enumeration N T n)
    (F : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hs : LightWeightedBankSweep.Stages E (fun k => forwardStage k F) base N μ) :
    ∀ j<n, μ (base+N*n+j)=ThreeSum.TernaryEuler.binomialZeta F (E.word j) := by sorry
