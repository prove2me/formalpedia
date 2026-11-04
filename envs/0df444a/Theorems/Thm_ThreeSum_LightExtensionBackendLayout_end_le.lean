-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionBackendLayout_end_le
-- name    : ThreeSum.LightExtensionBackendLayout.end_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:15.780388+00:00
-- url     : https://prove2.me/theorems/790a4a64-981d-4b9d-a9af-1f073d10e651
-- title:
--   Light Extension Backend Layout: end le
-- statement:
--   The Light Extension Backend Layout construction uses the end le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionBackendLayout.lean#L42-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionBackendLayout.lean#L42-L61

import Definitions.Def_Submission_ThreeSum_LightExtensionBackend
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget
import Definitions.Def_Submission_ThreeSum_LightIrreducibleBudget
import Definitions.Def_Submission_ThreeSum_LightExtensionBackendLayout
set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionBackendLayout
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

theorem ThreeSum.LightExtensionBackendLayout.end_le (base d p q J : ℕ) : sum base d q J+2*d≤base+reserve d p q J := by sorry
