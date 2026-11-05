-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run_scaled
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorFactory.Ready.run_scaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:01:04.858864+00:00
-- url     : https://prove2.me/theorems/0f6b15d9-0d72-4b6c-8ea2-7a75936546c6
-- title:
--   run_scaled
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorFactoryScaled.lean#L20-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorFactoryScaled.lean#L20-L45

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensorScaled
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorFactory
open Light TernaryJointType TernaryPairedTensor
open scoped BigOperators

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorFactory.Ready.run_scaled {N a b d K J config ls rs tensorBase quad powers cols potPowers U : ℕ}
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
