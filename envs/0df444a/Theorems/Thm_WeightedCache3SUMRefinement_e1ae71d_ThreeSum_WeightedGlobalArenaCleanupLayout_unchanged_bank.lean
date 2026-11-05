-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaCleanupLayout_unchanged_bank
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCleanupLayout.unchanged_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:00:44.1247+00:00
-- url     : https://prove2.me/theorems/3942876d-5c6f-404e-a312-1c788b854714
-- title:
--   unchanged_bank
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaCleanupLayout.lean#L39-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaCleanupLayout.lean#L39-L52

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCleanupLayout
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCleanupLayout
open Light WeightedGlobalArenaLayout LightOriginalSurvivors LightOriginalSurvivorPair
set_option maxHeartbeats 2000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaCleanupLayout.unchanged_bank {free C aBase nA bBase nB cBase nC q L : ℕ}
    {keysB keysC : ℕ→ℕ} {μ ν : ℕ→ℤ}
    (hnB : nB≤C) (hnC : nC≤C)
    (h : (layout free C aBase nA bBase nB cBase nC q L).Unchanged keysB keysC μ ν)
    {x : ℕ} (hlo : addr free C 11≤x) (hhi : x<addr free C 16) : ν x=μ x := by sorry
