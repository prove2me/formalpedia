-- Prove2me | Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run_physical
-- name    : ThreeSum.WeightedSourceCountExecutionFactory.Ready.run_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:52:27.933581+00:00
-- url     : https://prove2.me/theorems/9514d442-c293-4ef6-8c88-7cf4fe7f15e5
-- title:
--   Ready: run physical
-- statement:
--   The same actual host receipt has literal original-record weighted pair
--   semantics, including equal-valued and repeated source occurrences.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountExecutionFactory.lean#L103-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountExecutionFactory.lean#L103-L119

import Definitions.Def_Submission_Weighted_CountExecutionFactory
import Definitions.Def_Submission_Weighted_SourceCountExecutionFactory
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType

theorem ThreeSum.WeightedSourceCountExecutionFactory.Ready.run_physical {N a b : ℕ} {S : Setup N} {lim : Limits} {d : ℕ} {μ : ℕ→ℤ}
    {leftWeight rightWeight : ℕ→ℤ} (H : Ready S lim d μ leftWeight rightWeight)
    (hleft : ∀ pair∈S.left.records, TernaryBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hright : ∀ pair∈S.right.records, TernaryBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ j<S.front.count, TernaryBank.rank (S.front.Q j)=a+b) :
    Meets lim S.program 134 d S.argv μ S.runtime
      (fun _ ν => Kept μ ν S.left.base0 ∧ ∀ j<S.front.count,
        ν (S.front.dst+j)=TernaryConvolution.factorial (S.front.Q j)*
          TernaryWeightedPhysicalSources.pairWeight
            (TernarySourceHostModel.channel S.left.records S.left.group (S.front.group j))
            (TernarySourceHostModel.channel S.right.records S.right.group (S.front.group j))
            (fun pair => S.front.E.word (S.left.key pair.2))
            (fun pair => S.front.E.word (S.right.key pair.2))
            (fun pair => leftWeight pair.1) (fun pair => rightWeight pair.1) (S.front.Q j)) := by sorry
