-- Prove2me | Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_run_physical
-- name    : ThreeSum.WeightedSourceCountExecutionFactory.Seed.run_physical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:02:14.751558+00:00
-- url     : https://prove2.me/theorems/828c0650-d7c9-44e9-8c3d-2553bb6c4c48
-- title:
--   Seed: run physical
-- statement:
--   The Seed construction uses the run physical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySourceCountWeightSeed.lean#L65-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySourceCountWeightSeed.lean#L65-L84

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountExecutionFactory
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run_physical

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType

theorem ThreeSum.WeightedSourceCountExecutionFactory.Seed.run_physical {N a b : ℕ} {S : Setup N} {lim : Limits} {d boundary : ℕ}
    {μ ν : ℕ→ℤ} {leftWeight rightWeight : ℕ→ℤ}
    (H : Seed S lim d boundary μ leftWeight rightWeight) (hkeep : Kept μ ν boundary)
    (hleftRead : ∀ i<S.left.NL, ν (S.left.weightBase+i)=leftWeight i)
    (hrightRead : ∀ i<S.right.NL, ν (S.right.weightBase+i)=rightWeight i)
    (hleft : ∀ pair∈S.left.records, WeightedGlobalBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hright : ∀ pair∈S.right.records, WeightedGlobalBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ j<S.front.count, WeightedGlobalBank.rank (S.front.Q j)=a+b) :
    Meets lim S.program 134 d S.argv ν S.runtime
      (fun _ ξ => Kept ν ξ boundary ∧ ∀ j<S.front.count,
        ξ (S.front.dst+j)=TernaryConvolution.factorial (S.front.Q j)*
          TernaryWeightedPhysicalSources.pairWeight
            (TernarySourceHostModel.channel S.left.records S.left.group (S.front.group j))
            (TernarySourceHostModel.channel S.right.records S.right.group (S.front.group j))
            (fun pair => S.front.E.word (S.left.key pair.2))
            (fun pair => S.front.E.word (S.right.key pair.2))
            (fun pair => leftWeight pair.1) (fun pair => rightWeight pair.1) (S.front.Q j)) := by sorry
