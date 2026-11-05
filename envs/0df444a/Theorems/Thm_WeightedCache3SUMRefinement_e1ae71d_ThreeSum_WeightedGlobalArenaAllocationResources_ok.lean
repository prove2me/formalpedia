-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaAllocationResources_ok
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaAllocationResources.ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T14:34:19.270989+00:00
-- url     : https://prove2.me/theorems/201f2cda-5ac2-4a14-9db9-dff4ea4c59a0
-- title:
--   ok
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaAllocationResources.lean#L21-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaAllocationResources.lean#L21-L33

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaAllocationResources
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaAllocationResources
open Light WeightedGlobalArenaLayout WeightedGlobalArenaAllocation
open WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaAllocationResources.ok {maps : Fin F→Weight m p} {τ cap M b K H drift scale n U free d : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) {lim : Limits}
    (H : (need A n U).Ok lim free d) :
    finish free (capacity A.D A.E (n+U))≤lim.space ∧
    (capacity A.D A.E (n+U) : ℤ)≤lim.word ∧
    d+100+capacity A.D A.E (n+U)≤lim.depth ∧ (lim.space : ℤ)≤lim.word := by sorry
