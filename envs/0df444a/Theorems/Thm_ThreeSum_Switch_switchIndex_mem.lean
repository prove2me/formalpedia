-- Prove2me | Theorems.Thm_ThreeSum_Switch_switchIndex_mem
-- name    : ThreeSum.Switch.switchIndex_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:36.527422+00:00
-- url     : https://prove2.me/theorems/3b74ae26-8ac2-4438-8d97-82f64b63c65b
-- title:
--   Switch: switch Index mem
-- statement:
--   The Switch construction uses the switch Index mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L45-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean#L45-L48

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0

theorem ThreeSum.Switch.switchIndex_mem {J j r : ℕ} (h : (candidates J j r).Nonempty) :
    switchIndex J j r ∈ candidates J j r := by sorry
