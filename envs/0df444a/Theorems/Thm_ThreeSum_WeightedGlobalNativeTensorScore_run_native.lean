-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalNativeTensorScore_run_native
-- name    : ThreeSum.WeightedGlobalNativeTensorScore.run_native
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:07:03.370966+00:00
-- url     : https://prove2.me/theorems/640d7d67-7c4f-495f-9e89-920ebed10d36
-- title:
--   Weighted Global Native Tensor Score: run native
-- statement:
--   No finite tensor-model equality remains among the assumptions: original
--   physical record multiplicities and the four channels are identified here.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTensorScore.lean#L89-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativeTensorScore.lean#L89-L107

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeTensorScore
open TernaryJointType WeightedGlobalNativePairMoments
open LightWeightedGlobalTensorFactory LightTernaryPairedPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000

theorem ThreeSum.WeightedGlobalNativeTensorScore.run_native {N a b d K J config ls rs tensorBase quad powers cols potPowers U t : ℕ}
    {S : WeightedSourceCountExecutionFactory.Setup N} {lim : Light.Limits} {μ : ℕ→ℤ}
    {L R : ℕ→ℕ→ℤ} {V : ℤ}
    (H : Ready S lim d K J config ls rs tensorBase quad powers cols potPowers μ L R U V)
    (hleft : ∀ pair∈S.left.records, WeightedGlobalBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hright : ∀ pair∈S.right.records, WeightedGlobalBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ j<S.front.count, WeightedGlobalBank.rank (S.front.Q j)=a+b)
    (hcountTwo : ∀ j<S.front.count, digitCount (S.front.Q j) 2=t) :
    Light.Meets lim (program S K) 150 d
      [config,ls,S.left.NL,rs,S.right.NL,J,S.left.weightBase,S.right.weightBase,
        tensorBase,S.front.count,S.front.dst,quad,powers,cols,potPowers] μ
      (LightWeightedGlobalTensorDriver.time K J S.left.NL S.right.NL S.front.count S.runtime)
      (fun r ν => r=((2 : ℤ)^t)^K*(pairedPotential S K J L R : ℤ) ∧
        LightWeightedGlobalTensorDriver.InputKept μ ν quad tensorBase S.front.count ((J+2)^4)) := by sorry
