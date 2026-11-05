-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSourceCountExecutionFactory.Ready.run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:44:31.431293+00:00
-- url     : https://prove2.me/theorems/df5d59ea-8263-4259-b3ad-1385815c0cb4
-- title:
--   run
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/SourceCountExecutionFactory.lean#L60-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/SourceCountExecutionFactory.lean#L60-L99

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountExecutionFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountExecutionFactory
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedCountExecutionFactory_Ready_run

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSourceCountExecutionFactory.Ready.run {N : ℕ} {S : Setup N} {lim : Limits} {d : ℕ} {μ : ℕ→ℤ}
    {leftWeight rightWeight : ℕ→ℤ} (H : Ready S lim d μ leftWeight rightWeight) :
    Meets lim S.program 134 d S.argv μ S.runtime
      (fun _ ν => Kept μ ν S.left.base0 ∧ ∀ j<S.front.count,
        ν (S.front.dst+j)=LightWeightedWantedRows.score
          (S.F leftWeight) (S.G rightWeight) S.front.group S.front.Q j) := by sorry
