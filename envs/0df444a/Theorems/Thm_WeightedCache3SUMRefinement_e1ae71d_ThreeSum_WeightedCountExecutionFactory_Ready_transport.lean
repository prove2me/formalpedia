-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedCountExecutionFactory_Ready_transport
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedCountExecutionFactory.Ready.transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:27:15.263533+00:00
-- url     : https://prove2.me/theorems/c84c7b6c-ec42-44e9-a40b-889f1bb3fc4a
-- title:
--   transport
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/CountExecutionFactory.lean#L106-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/CountExecutionFactory.lean#L106-L121

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrontendResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountExecutionFactory
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_transport

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedCountExecutionFactory
open Light TernaryJointType TernaryBank TernaryCodeSemantics
open WeightedBankStageModel
open WeightedBankEnumeration (cacheCost)
open LightWeightedNearPair LightWeightedWantedRowDispatch LightWeightedPreparedState
open LightSubsetAddress

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedCountExecutionFactory.Ready.transport {N : ℕ} {S : Setup N} {lim : Limits} {d keep : ℕ}
    {μ ν : ℕ→ℤ} {F G : ℕ→TritWord N→ℤ}
    (H : Ready S lim d μ F G) (hkeep : Kept μ ν keep)
    (hcodes : S.f.bank+S.f.nb≤keep) (hrecords : S.records+3*S.count≤keep) :
    Ready S lim d ν F G := by sorry
