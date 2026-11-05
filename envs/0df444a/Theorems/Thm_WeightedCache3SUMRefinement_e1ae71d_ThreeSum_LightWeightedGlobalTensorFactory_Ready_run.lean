-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorFactory.Ready.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:31:38.875583+00:00
-- url     : https://prove2.me/theorems/824b4f07-eb09-4a32-80a7-825b111afa21
-- title:
--   run
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorFactoryReady.lean#L62-L142
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryTensorFactoryReady.lean#L62-L142

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorFactory
open Light TernaryJointType
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalTensorFactory.Ready.run {N a b d K J config ls rs tensor quad powers cols potPowers U : ℕ}
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
