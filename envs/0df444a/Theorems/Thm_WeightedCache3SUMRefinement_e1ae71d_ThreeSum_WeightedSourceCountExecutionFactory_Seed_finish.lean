-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSourceCountExecutionFactory.Seed.finish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:40:02.116207+00:00
-- url     : https://prove2.me/theorems/85a54f05-3888-46cc-bfaf-778b5d3ba8cd
-- title:
--   finish
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySourceCountWeightSeed.lean#L53-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernarySourceCountWeightSeed.lean#L53-L63

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountExecutionFactory
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSourceCountExecutionFactory.Seed.finish {N : ℕ} {S : Setup N} {lim : Limits} {d boundary : ℕ}
    {μ ν : ℕ→ℤ} {leftWeight rightWeight : ℕ→ℤ}
    (H : Seed S lim d boundary μ leftWeight rightWeight) (hkeep : Kept μ ν boundary)
    (hleftRead : ∀ i<S.left.NL, ν (S.left.weightBase+i)=leftWeight i)
    (hrightRead : ∀ i<S.right.NL, ν (S.right.weightBase+i)=rightWeight i) :
    Ready S lim d ν leftWeight rightWeight := by sorry
