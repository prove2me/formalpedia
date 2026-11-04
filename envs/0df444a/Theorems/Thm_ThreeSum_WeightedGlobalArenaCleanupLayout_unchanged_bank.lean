-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCleanupLayout_unchanged_bank
-- name    : ThreeSum.WeightedGlobalArenaCleanupLayout.unchanged_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:27:42.807362+00:00
-- url     : https://prove2.me/theorems/fc597f54-ec28-4a0b-b2fe-8139ecbfe9cf
-- title:
--   Weighted Global Arena Cleanup Layout: unchanged bank
-- statement:
--   The Weighted Global Arena Cleanup Layout construction uses the unchanged bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCleanupLayout.lean#L39-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCleanupLayout.lean#L39-L52

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCleanupLayout
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_layout
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_layout

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaCleanupLayout
open Light WeightedGlobalArenaLayout LightOriginalSurvivors LightOriginalSurvivorPair
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalArenaCleanupLayout.unchanged_bank {free C aBase nA bBase nB cBase nC q L : ℕ}
    {keysB keysC : ℕ→ℕ} {μ ν : ℕ→ℤ}
    (hnB : nB≤C) (hnC : nC≤C)
    (h : (layout free C aBase nA bBase nB cBase nC q L).Unchanged keysB keysC μ ν)
    {x : ℕ} (hlo : addr free C 11≤x) (hhi : x<addr free C 16) : ν x=μ x := by sorry
