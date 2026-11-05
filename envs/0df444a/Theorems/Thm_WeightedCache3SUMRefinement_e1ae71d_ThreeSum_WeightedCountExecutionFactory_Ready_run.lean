-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedCountExecutionFactory_Ready_run
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedCountExecutionFactory.Ready.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:27:00.286369+00:00
-- url     : https://prove2.me/theorems/9c89d8f7-6796-4bce-adda-69bd778faa91
-- title:
--   run
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/CountExecutionFactory.lean#L94-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/CountExecutionFactory.lean#L94-L104

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrontendResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountExecutionFactory
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedCountExecutionFactory.Ready.run {N : ℕ} {S : Setup N} {lim : Limits} {d : ℕ} {μ : ℕ→ℤ}
    {F G : ℕ→TritWord N→ℤ} (H : Ready S lim d μ F G)
    (hsourceF : LightWeightedSourceCountHost.BankReads μ S.fsource S.groups S.f.nb
      (fun g r => F g (S.E.word r)))
    (hsourceG : LightWeightedSourceCountHost.BankReads μ S.gsource S.groups S.f.nb
      (fun g r => G g (S.E.word r))) :
    Meets lim LightWeightedCountFrontend.program 63 d S.argv μ S.runtime
      (fun _ ν => Kept μ ν S.keyBase ∧ ∀ j<S.count,
        ν (S.dst+j)=LightWeightedWantedRows.score F G S.group S.Q j) := by sorry
