-- Prove2me | Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
-- name    : ThreeSum.WeightedCountExecutionFactory.Ready.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:20:11.849203+00:00
-- url     : https://prove2.me/theorems/42286389-ba38-44a5-a771-1bcb75e5fa26
-- title:
--   Ready: run
-- statement:
--   All source-value reads are consequences of actual source receipts. All
--   remaining premises are pure finite, memory, or resource bounds.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/CountExecutionFactory.lean#L94-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/CountExecutionFactory.lean#L94-L104

import Definitions.Def_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_Submission_Weighted_FrontendResources
import Definitions.Def_Submission_Weighted_CountExecutionFactory
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedCountExecutionFactory
open Light TernaryJointType TernaryBank TernaryCodeSemantics
open WeightedBankStageModel
open WeightedBankEnumeration (cacheCost)
open LightWeightedNearPair LightWeightedWantedRowDispatch LightWeightedPreparedState
open LightSubsetAddress

theorem ThreeSum.WeightedCountExecutionFactory.Ready.run {N : ℕ} {S : Setup N} {lim : Limits} {d : ℕ} {μ : ℕ→ℤ}
    {F G : ℕ→TritWord N→ℤ} (H : Ready S lim d μ F G)
    (hsourceF : LightWeightedSourceCountHost.BankReads μ S.fsource S.groups S.f.nb
      (fun g r => F g (S.E.word r)))
    (hsourceG : LightWeightedSourceCountHost.BankReads μ S.gsource S.groups S.f.nb
      (fun g r => G g (S.E.word r))) :
    Meets lim LightWeightedCountFrontend.program 63 d S.argv μ S.runtime
      (fun _ ν => Kept μ ν S.keyBase ∧ ∀ j<S.count,
        ν (S.dst+j)=LightWeightedWantedRows.score F G S.group S.Q j) := by sorry
