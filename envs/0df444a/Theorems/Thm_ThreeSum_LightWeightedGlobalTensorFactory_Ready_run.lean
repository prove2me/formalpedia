-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
-- name    : ThreeSum.LightWeightedGlobalTensorFactory.Ready.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:53:08.66399+00:00
-- url     : https://prove2.me/theorems/2d7e80de-5d28-4910-8210-f655722236ea
-- title:
--   Ready: run
-- statement:
--   Complete actual tensor execution from pure memory, finite-model and
--   resource readiness. No execution premise or oracle occurs in this contract.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorFactoryReady.lean#L62-L142
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorFactoryReady.lean#L62-L142

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactory
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalTensorFactory
open Light TernaryJointType
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalTensorFactory.Ready.run {N a b d K J config ls rs tensor quad powers cols potPowers U : ℕ}
    {S : WeightedSourceCountExecutionFactory.Setup N} {lim : Limits} {μ : ℕ→ℤ}
    {L R : ℕ→ℕ→ℤ} {V : ℤ}
    (H : Ready S lim d K J config ls rs tensor quad powers cols potPowers μ L R U V)
    (hleft : ∀ pair∈S.left.records, WeightedGlobalBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hright : ∀ pair∈S.right.records, WeightedGlobalBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ j<S.front.count, WeightedGlobalBank.rank (S.front.Q j)=a+b) :
    Meets lim (program S K) 150 d
      [config,ls,S.left.NL,rs,S.right.NL,J,S.left.weightBase,S.right.weightBase,
        tensor,S.front.count,S.front.dst,quad,powers,cols,potPowers] μ
      (LightWeightedGlobalTensorDriver.time K J S.left.NL S.right.NL S.front.count S.runtime)
      (fun r ν => r=LightTernaryPairedPotentialBatch.total K tensor (J+2) ν S.front.count ∧
        (∀ w<S.front.count, ∀ q<(J+2)^4, ν (tensor+w*((J+2)^4)+q)=score S J L R w q) ∧
        LightWeightedGlobalTensorDriver.InputKept μ ν quad tensor S.front.count ((J+2)^4)) := by sorry
