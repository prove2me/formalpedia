-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaAllocationResources_ok
-- name    : ThreeSum.WeightedGlobalArenaAllocationResources.ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:09:48.669667+00:00
-- url     : https://prove2.me/theorems/f78b72ce-c602-42e8-9351-5f5d2eedfa4b
-- title:
--   Weighted Global Arena Allocation Resources: ok
-- statement:
--   The Weighted Global Arena Allocation Resources construction uses the ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocationResources.lean#L21-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaAllocationResources.lean#L21-L33

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocationResources
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaAllocationResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation
open WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaAllocationResources.ok {maps : Fin F→Weight m p} {τ cap M b K H drift scale n U free d : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) {lim : Limits}
    (H : (need A n U).Ok lim free d) :
    finish free (capacity A.D A.E (n+U))≤lim.space ∧
    (capacity A.D A.E (n+U) : ℤ)≤lim.word ∧
    d+100+capacity A.D A.E (n+U)≤lim.depth ∧ (lim.space : ℤ)≤lim.word := by sorry
