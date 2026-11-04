-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_visits_pos
-- name    : ThreeSum.TernaryFrozenQueryCost.visits_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:04.686225+00:00
-- url     : https://prove2.me/theorems/8061ae07-27d3-42f8-91df-8b48f1afa76e
-- title:
--   Ternary Frozen Query Cost: visits pos
-- statement:
--   The Ternary Frozen Query Cost construction uses the visits pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L21-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L21-L22

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryCost.visits_pos (qs : List ℕ) (D : ℕ) : 1≤TernaryNearEnumeration.visits qs D := by sorry
