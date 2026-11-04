-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaCapacity_exists_capacity
-- name    : ThreeSum.WeightedGlobalArenaCapacity.exists_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:54:26.040225+00:00
-- url     : https://prove2.me/theorems/e1a5f9f8-b004-4aa3-aa89-d4fc5737c8bd
-- title:
--   Weighted Global Arena Capacity: exists capacity
-- statement:
--   The Weighted Global Arena Capacity construction uses the exists capacity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCapacity.lean#L27-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaCapacity.lean#L27-L36

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCapacity
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaCapacity
open Light WeightedGlobalArenaLayout

theorem ThreeSum.WeightedGlobalArenaCapacity.exists_capacity {need : ℕ→ℕ→Need} (h : PolyNeed need) :
    ∃ D E : ℕ, ∀ n U,
      (need n U).word≤capacity D E (n+U) ∧
      (need n U).cells≤capacity D E (n+U) ∧
      (need n U).depth≤capacity D E (n+U) := by sorry
