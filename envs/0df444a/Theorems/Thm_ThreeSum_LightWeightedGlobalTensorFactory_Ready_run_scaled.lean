-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run_scaled
-- name    : ThreeSum.LightWeightedGlobalTensorFactory.Ready.run_scaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:42:49.482609+00:00
-- url     : https://prove2.me/theorems/cbe5e09e-e5d1-4ab0-b098-f219bbe58e3d
-- title:
--   Ready: run scaled
-- statement:
--   The checked scalar is exactly the common wanted factorial to the Kth
--   power times the actual original-endpoint paired potential. The model
--   premise is an equality of finite weighted record sums, not execution or
--   solver advice.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorFactoryScaled.lean#L20-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorFactoryScaled.lean#L20-L45

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensorScaled
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalTensorFactory
open Light TernaryJointType TernaryPairedTensor
open scoped BigOperators

theorem ThreeSum.LightWeightedGlobalTensorFactory.Ready.run_scaled {N a b d K J config ls rs tensorBase quad powers cols potPowers U : ℕ}
    {S : WeightedSourceCountExecutionFactory.Setup N} {lim : Limits} {μ : ℕ→ℤ}
    {L R : ℕ→ℕ→ℤ} {V : ℤ}
    (H : Ready S lim d K J config ls rs tensorBase quad powers cols potPowers μ L R U V)
    (hleft : ∀ pair∈S.left.records, WeightedGlobalBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hright : ∀ pair∈S.right.records, WeightedGlobalBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ j<S.front.count, WeightedGlobalBank.rank (S.front.Q j)=a+b)
    (P : Fin S.front.count→Type*) [∀ i, Fintype (P i)]
    (A B : ∀ i, P i→Fin (J+2)→ℤ) (s : ℤ)
    (hModel : ∀ (i : Fin S.front.count) (a b c e : Fin (J+2)),
      score S J L R i.val (LightTernaryPairedPolynomial.tensorIndex (J+2) a.val b.val c.val e.val)=
        s*tensor (A i) (B i) a b c e) :
    Meets lim (program S K) 150 d
      [config,ls,S.left.NL,rs,S.right.NL,J,S.left.weightBase,S.right.weightBase,
        tensorBase,S.front.count,S.front.dst,quad,powers,cols,potPowers] μ
      (LightWeightedGlobalTensorDriver.time K J S.left.NL S.right.NL S.front.count S.runtime)
      (fun r ν => r=s^K*((∑ i : Fin S.front.count, ∑ e : Fin K→P i,
          TernaryPairedPotential.rowWeight
            (Sum.elim (fun j => A i (e j)) (fun j => B i (e j)))) : ℤ) ∧
        LightWeightedGlobalTensorDriver.InputKept μ ν quad tensorBase S.front.count ((J+2)^4)) := by sorry
