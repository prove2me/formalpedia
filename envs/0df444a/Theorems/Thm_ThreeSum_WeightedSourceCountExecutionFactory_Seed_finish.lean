-- Prove2me | Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish
-- name    : ThreeSum.WeightedSourceCountExecutionFactory.Seed.finish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:01:25.154875+00:00
-- url     : https://prove2.me/theorems/4cc0eed5-dc23-465a-8797-f94312a5feb5
-- title:
--   Seed: finish
-- statement:
--   The Seed construction uses the finish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySourceCountWeightSeed.lean#L53-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernarySourceCountWeightSeed.lean#L53-L63

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountExecutionFactory
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType

theorem ThreeSum.WeightedSourceCountExecutionFactory.Seed.finish {N : ℕ} {S : Setup N} {lim : Limits} {d boundary : ℕ}
    {μ ν : ℕ→ℤ} {leftWeight rightWeight : ℕ→ℤ}
    (H : Seed S lim d boundary μ leftWeight rightWeight) (hkeep : Kept μ ν boundary)
    (hleftRead : ∀ i<S.left.NL, ν (S.left.weightBase+i)=leftWeight i)
    (hrightRead : ∀ i<S.right.NL, ν (S.right.weightBase+i)=rightWeight i) :
    Ready S lim d ν leftWeight rightWeight := by sorry
