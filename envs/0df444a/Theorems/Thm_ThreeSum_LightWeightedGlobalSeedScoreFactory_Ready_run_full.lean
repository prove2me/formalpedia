-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalSeedScoreFactory_Ready_run_full
-- name    : ThreeSum.LightWeightedGlobalSeedScoreFactory.Ready.run_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:29:19.170972+00:00
-- url     : https://prove2.me/theorems/2816a1c1-360b-4dfb-9ad9-d6b531bd1c67
-- title:
--   Ready: run full
-- statement:
--   The Ready construction uses the run full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFull.lean#L31-L143
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernarySeedScoreFull.lean#L31-L143

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFactory
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedScoreFull
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_Reads_update
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_Reads_update

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalSeedScoreFactory
open Light
open scoped BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
variable {lim : Limits}

theorem ThreeSum.LightWeightedGlobalSeedScoreFactory.Ready.run_full {C : Config} [Fact C.p.Prime] {D : Data C}
    {depth R mapRadix cap V K N U a b : ℕ} {host : WeightedSourceCountExecutionFactory.Setup N}
    {L Rvalues : ℕ → ℕ → ℤ} {scoreBound : ℤ} {raws : List ℤ} {words maps : List ℕ} {μ : ℕ → ℤ}
    (G : Ready C D lim depth R mapRadix cap V K N U host L Rvalues scoreBound raws words maps μ)
    (hretain : C.wanted+(D.wantedRows R mapRadix raws words maps).length≤C.tensor)
    (hleft : ∀pair∈host.left.records, WeightedGlobalBank.rank (host.front.E.word (host.left.key pair.2))=a)
    (hright : ∀pair∈host.right.records, WeightedGlobalBank.rank (host.front.E.word (host.right.key pair.2))=b)
    (hQ : ∀j<host.front.count, WeightedGlobalBank.rank (host.front.Q j)=a+b)
    (P : Fin host.front.count → Type*) [∀i, Fintype (P i)]
    (A B : ∀i, P i → Fin (C.J+2) → ℤ) (s : ℤ)
    (hModel : ∀(i : Fin host.front.count) (a b c e : Fin (C.J+2)),
      LightWeightedGlobalTensorFactory.score host C.J L Rvalues i.val
        (LightTernaryPairedPolynomial.tensorIndex (C.J+2) a.val b.val c.val e.val)=
        s*TernaryPairedTensor.tensor (A i) (B i) a b c e)
    (hPairedWord : |s^K*((∑i : Fin host.front.count, ∑e : Fin K→P i,
      TernaryPairedPotential.rowWeight (Sum.elim (fun j => A i (e j)) (fun j => B i (e j)))) : ℤ)|≤lim.word) :
    Meets lim (LightWeightedGlobalSeedScore.program C.p R mapRadix K raws words maps
      host.left.xs host.left.ys host.left.zs host.right.xs host.right.ys host.right.zs)
      176 depth C.argv μ (runtime D host K R mapRadix cap V raws words maps)
      (fun r ν => r=D.flag ∧ ∃ξ, (KeptInput C μ ξ ∧ LightWeightedGlobalSeedScoreFull.Outputs C D R mapRadix raws words maps ξ) ∧ ν=
        Function.update (Function.update (Function.update (Function.update ξ
          (C.flags+C.seed) D.flag) (C.scoreB+C.seed) D.collisionB) (C.scoreC+C.seed) D.collisionC)
          (C.scorePaired+C.seed) (s^K*((∑i : Fin host.front.count, ∑e : Fin K→P i,
            TernaryPairedPotential.rowWeight (Sum.elim (fun j => A i (e j)) (fun j => B i (e j)))) : ℤ))) := by sorry
