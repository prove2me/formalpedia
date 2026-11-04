-- Prove2me | Theorems.Thm_ThreeSum_TernaryHybridCosts_time_of_large
-- name    : ThreeSum.TernaryHybridCosts.time_of_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:45:18.733203+00:00
-- url     : https://prove2.me/theorems/828e21ab-68c8-4fba-adbc-615870df4b5f
-- title:
--   Ternary Hybrid Costs: time of large
-- statement:
--   The Ternary Hybrid Costs construction uses the time of large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCosts.lean#L21-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryHybridCosts.lean#L21-L25

import Definitions.Def_Submission_ThreeSum_TernaryHybridCore
import Definitions.Def_Submission_ThreeSum_TernaryEndBridge
import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryHybridCosts
open Light StageBounds Filter
noncomputable section

theorem ThreeSum.TernaryHybridCosts.time_of_large {T : ℕ → ℕ} {κ cutoff n U : ℕ}
    (hn : cutoff ≤ n) (hU : U ≤ n^κ) :
    TernaryHybridCore.time T κ cutoff n U = fastTime T κ n := by sorry
