-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run_native
-- name    : ThreeSum.LightWeightedGlobalSeedScoreFactory.Ready.run_native
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:42:05.550962+00:00
-- url     : https://prove2.me/theorems/65ca0992-e0f1-47e3-9275-fddde0050c29
-- title:
--   Ready: run native
-- statement:
--   Original-pair semantics require only the actual homogeneous output type;
--   no external finite tensor-model equality is supplied.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L510-L535
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFactory.lean#L510-L535

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScore
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalDigitSpan
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_WeightedGlobalNativeTensorScore_run_native

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}
open scoped BigOperators

theorem ThreeSum.LightWeightedGlobalSeedScoreFactory.Ready.run_native {C : Config} [Fact C.p.Prime] {D : Data C}
    {depth R mapRadix cap V K N U a b t : ℕ} {host : WeightedSourceCountExecutionFactory.Setup N}
    {L Rvalues : ℕ → ℕ → ℤ} {scoreBound : ℤ} {raws : List ℤ} {words maps : List ℕ} {μ : ℕ → ℤ}
    (G : Ready C D lim depth R mapRadix cap V K N U host L Rvalues scoreBound raws words maps μ)
    (hleft : ∀pair∈host.left.records, WeightedGlobalBank.rank (host.front.E.word (host.left.key pair.2))=a)
    (hright : ∀pair∈host.right.records, WeightedGlobalBank.rank (host.front.E.word (host.right.key pair.2))=b)
    (hQ : ∀j<host.front.count, WeightedGlobalBank.rank (host.front.Q j)=a+b)
    (hcountTwo : ∀j<host.front.count, TernaryJointType.digitCount (host.front.Q j) 2=t)
    (hPairedWord : |((2 : ℤ)^t)^K*(WeightedGlobalNativeTensorScore.pairedPotential host K C.J L Rvalues : ℤ)|≤lim.word) :
    Meets lim (LightWeightedGlobalSeedScore.program C.p R mapRadix K raws words maps
      host.left.xs host.left.ys host.left.zs host.right.xs host.right.ys host.right.zs)
      176 depth C.argv μ (runtime D host K R mapRadix cap V raws words maps)
      (fun r ν => r=D.flag ∧ ∃ξ, KeptInput C μ ξ ∧ ν=
        Function.update (Function.update (Function.update (Function.update ξ
          (C.flags+C.seed) D.flag) (C.scoreB+C.seed) D.collisionB) (C.scoreC+C.seed) D.collisionC)
          (C.scorePaired+C.seed) (((2 : ℤ)^t)^K*(WeightedGlobalNativeTensorScore.pairedPotential host K C.J L Rvalues : ℤ))) := by sorry
